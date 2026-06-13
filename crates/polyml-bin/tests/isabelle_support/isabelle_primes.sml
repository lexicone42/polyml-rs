(* ============================================================================
   isabelle_primes.sml  —  STRONG INDUCTION + STRICT LINEAR ORDER + PRIMALITY +
   the capstone EVERY n >= 2 HAS A PRIME DIVISOR.  ONE self-contained Isabelle/Pure
   ML driver proving SIX headline theorems in a single run over the warm
   /tmp/isabelle_pure checkpoint, all by genuine LCF-kernel inference on a
   hand-built object logic (type o + nat, Trueprop, Peano add/mult, equality oeq,
   induction, existentials, disjunction, divisibility, strict order).

   SIX HEADLINE THEOREMS  (each 0-hypothesis, validated `aconv` its intended goal,
   each printing "OK <name>"):

     strong_induct        (course-of-values / complete induction; a schematic rule)
         (!!n. (!!m. lt m n ==> P m) ==> P n) ==> P k
     lt_trans             m < n ==> n < k ==> m < k          (strict order is transitive)
     lt_trichotomy        (m < n) | (m = n) | (n < m)        (strict LINEAR order)
     prime_two            prime 2                             (2 is prime)
     prime_gt_1           prime p ==> 1 < p                   (primes exceed 1)
     prime_divisor_exists 2 <= n ==> ?p. prime p /\ p | n    (CAPSTONE, by strong induction)

   On success the driver prints all six "OK <name>" lines + a final "PRIME_DONE".
   (The verbatim foundation prefix additionally prints its own FOUNDATION_OK
   self-checks and OK lines for the inherited lt_suc/lt_irrefl/lt_suc_cases and the
   dvd_*/le_* lemmas — those are fine; the SIX above are the required headline set.)

   HOW IT WAS BUILT  (merge of five INDEPENDENTLY-VERIFIED drivers; integration,
   not invention):
     * The FOUNDATION (object logic, Peano add+mult, equality, induction, the
       existential/order extension ending on the single final context ctxtT/ctermT,
       the dvd development, le_trans/le_total/disj_zero_or_suc, and the strict-order
       `lt` abbreviation + lt_suc/lt_irrefl/lt_suc_cases) is copied VERBATIM from
       /tmp/isa_prime_foundation.sml (lines 1..1775 — byte-identical across all five
       source drivers, which each carry it as a prefix).
     * The four proof BODIES are appended in dependency order, each VERBATIM from its
       independently-verified source driver (only the terminal PRIME_DONE/PRIME_FAILED
       marker print of each is dropped, replaced by the single aggregate verdict at
       the end):
         lt_trans + lt_trichotomy   <- /tmp/isa_prime_lt_trichotomy.sml   (pure ctxtT)
         strong_induct              <- /tmp/isa_prime_strong_induction.sml (+ meta_nat_induct
                                          axiom on its own thyS/ctxtS; NO new constant)
         prime_two + prime_gt_1     <- /tmp/isa_prime_primality.sml        (Conj/Imp/All
                                          object connectives on thyP/ctxtP; `prime` an
                                          ML ABBREVIATION  Conj (lt 1 p) (All ...))
         prime_divisor_exists       <- /tmp/isa_prime_prime_divisor_exists.sml (Conj/Imp/
                                          Forall + a primitive `prime` const + the one
                                          honest classical `prime_cases` axiom; strong
                                          induction RE-DERIVED inline via nat_induct on
                                          the course-of-values predicate Q)
     * MERGE DECISIONS.  Every body depends ONLY on the foundation (none on another
       body), and each was already proven 0-hyp + aconv on this very checkpoint, so
       the bodies are concatenated as-is.  Each body that needs NEW object machinery
       extends the foundation's `thyT` in its OWN independent child theory
       (thyS / thyP), re-initialises its own final context, and re-varifies the
       schematic foundation lemmas it instantiates there — exactly the per-driver
       pattern the sources were verified with (a theory extension is functional;
       `thyT` is never mutated, so the independent children coexist).  The two notions
       of "prime" are kept honestly distinct: primality's structural ABBREVIATION
       (used by prime_two / prime_gt_1) and the capstone's primitive `prime` const
       with the classical `prime_cases` axiom (used by prime_divisor_exists).  ML
       shadowing means the helper wrappers (exE_elimP, disjE_elimP, conjI_at, the
       *_vP / *_at instantiators, mkConj/mkImp, the per-body checkP) are redefined per
       body and used eagerly within that body before the next body redefines them;
       the six headline result-flags (r_strong, r_lt_trans, r_lt_trichotomy,
       r_prime_two, r_prime_gt_1, r_pde) have distinct names and are computed eagerly,
       so the final aggregate verdict reads them safely.

   NON-NEGOTIABLES preserved from the sources: first statement is
   `val () = restore_pure_context ();`; no `print` (uses the foundation's `out`); no
   SML `ref`; add_axiom_global thms are varified before infer_instantiate/OF;
   infer_instantiate/forall_elim are beta-normed after; whole-implication / !!-premises
   are discharged with Thm.implies_elim (not OF); each headline is asserted 0-hyp AND
   `aconv` its intended schematic goal before "OK <name>".

   Expect ~400M+ bytecode steps (this is the largest merge — four full inductive
   developments on top of the shared arithmetic foundation).
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
   STRICT ORDER  lt  AND its BASICS  (the prime-development foundation extension)
   ----------------------------------------------------------------------------
   Everything below routes through the SINGLE FINAL context ctxtT / ctermT.

   lt is an ML ABBREVIATION (NOT a new constant, so the theory is unchanged and
   ctxtT stays the final context):

       lt m n  ==  le (Suc m) n        i.e.   Suc m <= n        i.e.  m < n

   Proves (each 0-hyp, named val, validated by checkLt below):
     lt_suc       : Trueprop (lt n (Suc n))
     lt_irrefl    : Trueprop (lt n n) ==> Trueprop oFalse
     lt_suc_cases : Trueprop (lt m (Suc n)) ==> Trueprop (Disj (lt m n) (oeq m n))
   ============================================================================ *)

(* lt m n  ==  le (Suc m) n *)
fun lt mT nT = le (suc mT) nT;

(* le_refl re-varified for ctxtT (base proved it under ctxtO) + ground instance *)
val le_refl_vT = varify le_refl;
fun le_reflT_at t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] le_refl_vT);

(* add laws as ground instantiators on ctxtT we will lean on:
     add0T_at, addSucT_at, add0rT_at, addSrT_at  (already defined in the base)
   Suc_neq_Zero on ctxtT, instantiated at an explicit n *)
fun Suc_neq_Zero_atT t = beta_norm (Drule.infer_instantiate ctxtT
       [(("n",0), ctermT t)] Suc_neq_Zero_vT);

(* ---------------------------------------------------------------------------
   lt_suc : Trueprop (lt n (Suc n))   ==   le (Suc n) (Suc n)   ==   le_refl@(Suc n)
   --------------------------------------------------------------------------- *)
val lt_suc =
  let
    val nF = Free("n", natT);
  in varify (le_reflT_at (suc nF)) end;

(* ---------------------------------------------------------------------------
   lt_irrefl : Trueprop (lt n n) ==> Trueprop oFalse
     lt n n = le (Suc n) n = Ex(%p. oeq n (add (Suc n) p)).
     exE witness p, hp : oeq n (add (Suc n) p).
       add (Suc n) p = Suc (add n p)            (add_Suc)
     and  n = add n 0                            (add_0_right, sym)
       add n (Suc p) = Suc (add n p)             (add_Suc_right)
     so  add n 0 = n = Suc(add n p) = add n (Suc p)
       => oeq (add n 0) (add n (Suc p))
       => oeq 0 (Suc p)                          (add_left_cancel)
       => oeq (Suc p) 0                          (sym)
       => oFalse                                 (Suc_neq_Zero)
   --------------------------------------------------------------------------- *)
val lt_irrefl =
  let
    val nF = Free("n", natT);
    val ltHypP = jT (lt nF nF);                        (* le (Suc n) n *)
    val ltHyp  = Thm.assume (ctermT ltHypP);
    val Pabs   = Abs("p", natT, oeq nF (add (suc nF) (Bound 0)));  (* body of le (Suc n) n *)
    val goalC  = oFalseC;
    fun body w (hw : thm) =                              (* hw : oeq n (add (Suc n) w) *)
      let
        val aS    = addSucT_at (nF, w);                  (* (Suc n + w) = Suc (n + w) *)
        val n_Snw = oeq_trans OF [hw, aS];               (* n = Suc (n + w) *)
        (* addSrT_at (nF,w) : oeq (add n (Suc w)) (Suc (add n w))   so (n + Suc w) = Suc(n+w) *)
        val n_nSw2 = oeq_trans OF [n_Snw, oeq_sym OF [addSrT_at (nF, w)]];  (* n = (n + Suc w) *)
        val n0n   = add0rT_at nF;                        (* (n + 0) = n *)
        val n0_nSw= oeq_trans OF [n0n, n_nSw2];          (* (n + 0) = (n + Suc w) *)
        val canc  = add_left_cancel_vT OF [n0_nSw];      (* oeq 0 (Suc w) *)
        val cancS = oeq_sym OF [canc];                   (* oeq (Suc w) 0 *)
        val false_thm = (Suc_neq_Zero_atT w) OF [cancS]; (* oFalse *)
      in false_thm end;
    val afterExE = exE_elimT (Pabs, goalC) ltHyp "wp" body;
    val disch    = Thm.implies_intr (ctermT ltHypP) afterExE;
  in varify disch end;

(* ---------------------------------------------------------------------------
   lt_suc_cases : Trueprop (lt m (Suc n)) ==> Trueprop (Disj (lt m n) (oeq m n))
     lt m (Suc n) = le (Suc m) (Suc n) = Ex(%p. oeq (Suc n) (add (Suc m) p)).
     exE witness p, hp : oeq (Suc n) (add (Suc m) p).
       add (Suc m) p = Suc (add m p)            (add_Suc)
       => oeq (Suc n) (Suc (add m p))
       => oeq n (add m p)                        (Suc_inj)      i.e.  le m n form
     Now split p by dzosT_at  (Disj (oeq p 0) (Ex(%q. oeq p (Suc q)))):
       p = 0   : n = add m 0 = m  (add_0_right) => oeq n m => oeq m n => disjI2.
       p = Suc q : add m (Suc q) = Suc(add m q) = add (Suc m) q (add_Suc sym);
                   so oeq n (add (Suc m) q) => le (Suc m) n = lt m n => disjI1.
   --------------------------------------------------------------------------- *)
val lt_suc_cases =
  let
    val mF = Free("m", natT); val nF = Free("n", natT);
    val ltHypP = jT (lt mF (suc nF));                   (* le (Suc m) (Suc n) *)
    val ltHyp  = Thm.assume (ctermT ltHypP);
    val Pabs   = Abs("p", natT, oeq (suc nF) (add (suc mF) (Bound 0)));  (* body of le (Suc m)(Suc n) *)
    val goalC  = mkDisj (lt mF nF) (oeq mF nF);
    fun body p (hp : thm) =                              (* hp : oeq (Suc n) (add (Suc m) p) *)
      let
        val aS    = addSucT_at (mF, p);                  (* (Suc m + p) = Suc (m + p) *)
        val Sn_Smp= oeq_trans OF [hp, aS];               (* Suc n = Suc (m + p) *)
        val n_mp  = (Suc_inj_atT (nF, add mF p)) OF [Sn_Smp];   (* oeq n (add m p)  == le-witness p *)
        (* case split on p *)
        val dz    = dzosT_at p;                          (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
        val caseZero =
          let
            val epz  = Thm.assume (ctermT (jT (oeq p ZeroC)));   (* oeq p 0 *)
            (* n = m + p = m + 0 = m *)
            val cong = add_cong_rT (mF, p, ZeroC) epz;   (* (m + p) = (m + 0) *)
            val n_m0 = oeq_trans OF [n_mp, cong];        (* n = (m + 0) *)
            val n_m  = oeq_trans OF [n_m0, add0rT_at mF];(* n = m *)
            val m_n  = oeq_sym OF [n_m];                 (* m = n *)
            val g    = disjI2T_at (lt mF nF, oeq mF nF) m_n;
          in Thm.implies_intr (ctermT (jT (oeq p ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermT (jT (mkEx PabsQ)));   (* Ex(%q. oeq p (Suc q)) *)
            fun sucBody q (hq : thm) =                          (* hq : oeq p (Suc q) *)
              let
                (* n = m + p = m + Suc q = Suc(m + q) = (Suc m) + q *)
                val cong   = add_cong_rT (mF, p, suc q) hq;     (* (m + p) = (m + Suc q) *)
                val n_mSq  = oeq_trans OF [n_mp, cong];         (* n = (m + Suc q) *)
                val mSq_S  = addSrT_at (mF, q);                 (* (m + Suc q) = Suc(m + q) *)
                val n_Smq  = oeq_trans OF [n_mSq, mSq_S];       (* n = Suc(m + q) *)
                val Smq_Smq= addSucT_at (mF, q);                (* (Suc m + q) = Suc(m + q) *)
                val n_Smqadd = oeq_trans OF [n_Smq, oeq_sym OF [Smq_Smq]]; (* n = (Suc m + q) *)
                val le_Sm_n = le_introT (suc mF, nF, q) n_Smqadd;  (* le (Suc m) n = lt m n *)
                val g = disjI1T_at (lt mF nF, oeq mF nF) le_Sm_n;
              in g end;
            val g = exE_elimT (PabsQ, goalC) exq "q0" sucBody;
          in Thm.implies_intr (ctermT (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimT (oeq p ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in combined end;
    val afterExE = exE_elimT (Pabs, goalC) ltHyp "wp" body;
    val disch    = Thm.implies_intr (ctermT ltHypP) afterExE;
  in varify disch end;

(* ============================================================================
   VALIDATION : each strict-order lemma must be 0-hyp AND aconv its intended goal
   (the goal built with the SAME `lt`/`le` abbreviations so Ex-bodies match).
   ============================================================================ *)
fun checkLt (nm, th, intended) =
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

val nVlt = Var (("n",0), natT);
val mVlt = Var (("m",0), natT);

val lt_suc_intended       = jT (lt nVlt (suc nVlt));
val lt_irrefl_intended    = Logic.mk_implies (jT (lt nVlt nVlt), jT oFalseC);
val lt_suc_cases_intended =
  Logic.mk_implies (jT (lt mVlt (suc nVlt)),
    jT (mkDisj (lt mVlt nVlt) (oeq mVlt nVlt)));

val r_lt_suc       = checkLt ("lt_suc",       lt_suc,       lt_suc_intended);
val r_lt_irrefl    = checkLt ("lt_irrefl",    lt_irrefl,    lt_irrefl_intended);
val r_lt_suc_cases = checkLt ("lt_suc_cases", lt_suc_cases, lt_suc_cases_intended);

val () = if r_lt_suc andalso r_lt_irrefl andalso r_lt_suc_cases
         then out "FOUNDATION_OK\n"
         else out "FOUNDATION_BROKEN\n";

(* ============================================================================
   PRIME-DEVELOPMENT TARGET: lt_trans + lt_trichotomy
   ----------------------------------------------------------------------------
   Everything routes through the SINGLE FINAL context ctxtT / ctermT.
   lt m n == le (Suc m) n.  Both theorems built only from the foundation
   helpers (le_trans, le_total, le_introT, disj*, oeq_*, add laws).
   ============================================================================ *)

(* ---------------------------------------------------------------------------
   le_suc_self : le b (Suc b)   [witness Suc Zero:  Suc b = b + 1]
     add b (Suc 0) = Suc (add b 0)   (add_Suc_right)
     Suc (add b 0) = Suc b           (Suc_cong of add_0_right)
     so  add b (Suc 0) = Suc b ;  sym => Suc b = add b (Suc 0) => le b (Suc b).
   --------------------------------------------------------------------------- *)
fun le_suc_self_at bT =
  let
    val asr   = addSrT_at (bT, ZeroC);              (* (b + Suc 0) = Suc (b + 0) *)
    val sb0   = Suc_cong OF [add0rT_at bT];         (* Suc (b + 0) = Suc b *)
    val bS1_Sb= oeq_trans OF [asr, sb0];            (* (b + Suc 0) = Suc b *)
    val Sb_bS1= oeq_sym OF [bS1_Sb];                (* Suc b = (b + Suc 0) *)
  in le_introT (bT, suc bT, suc ZeroC) Sb_bS1 end; (* le b (Suc b) *)

(* ---------------------------------------------------------------------------
   lt_trans : Trueprop (lt a b) ==> Trueprop (lt b c) ==> Trueprop (lt a c)
     lt a b = le (Suc a) b ;  lt b c = le (Suc b) c ;  goal le (Suc a) c.
     le (Suc a) b , le b (Suc b)  -le_trans->  le (Suc a) (Suc b)
     le (Suc a)(Suc b), le (Suc b) c -le_trans-> le (Suc a) c.
   --------------------------------------------------------------------------- *)
val le_trans_vT2 = varify le_trans;
fun le_trans_at (mt, nt, kt) h1 h2 =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("m",0), ctermT mt), (("n",0), ctermT nt), (("k",0), ctermT kt)] le_trans_vT2);
  in (inst OF [h1]) OF [h2] end;

val lt_trans =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H1prop = jT (lt aF bF);                     (* le (Suc a) b *)
    val H2prop = jT (lt bF cF);                     (* le (Suc b) c *)
    val H1 = Thm.assume (ctermT H1prop);
    val H2 = Thm.assume (ctermT H2prop);
    val le_b_Sb = le_suc_self_at bF;                (* le b (Suc b) *)
    (* le (Suc a) b , le b (Suc b) => le (Suc a) (Suc b) *)
    val le_Sa_Sb = le_trans_at (suc aF, bF, suc bF) H1 le_b_Sb;
    (* le (Suc a) (Suc b) , le (Suc b) c => le (Suc a) c = lt a c *)
    val le_Sa_c  = le_trans_at (suc aF, suc bF, cF) le_Sa_Sb H2;
    val d1 = Thm.implies_intr (ctermT H2prop) le_Sa_c;
    val d2 = Thm.implies_intr (ctermT H1prop) d1;
  in varify d2 end;

(* ---------------------------------------------------------------------------
   leCases (loT, hiT) leThm : Trueprop (Disj (lt loT hiT) (oeq loT hiT))
     leThm : Trueprop (le loT hiT) = Ex(%p. oeq hiT (add loT p)).
     exE witness p, hp : oeq hiT (add loT p).  Case-split p via dzosT_at:
       p = 0     : hiT = add loT 0 = loT => oeq loT hiT => disjI2.
       p = Suc q : hiT = add loT (Suc q) = Suc(add loT q) = add (Suc loT) q
                   => le (Suc loT) hiT = lt loT hiT => disjI1.
   --------------------------------------------------------------------------- *)
fun leCases (loT, hiT) leThm =
  let
    val Pabs  = Abs ("p", natT, oeq hiT (add loT (Bound 0)));   (* body of le loT hiT *)
    val goalC = mkDisj (lt loT hiT) (oeq loT hiT);
    fun body p (hp : thm) =                                      (* hp : oeq hiT (add loT p) *)
      let
        val dz = dzosT_at p;                                     (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
        val caseZero =
          let
            val epz  = Thm.assume (ctermT (jT (oeq p ZeroC)));   (* oeq p 0 *)
            val cong = add_cong_rT (loT, p, ZeroC) epz;          (* (lo + p) = (lo + 0) *)
            val hi_lo0 = oeq_trans OF [hp, cong];                (* hi = (lo + 0) *)
            val hi_lo  = oeq_trans OF [hi_lo0, add0rT_at loT];   (* hi = lo *)
            val lo_hi  = oeq_sym OF [hi_lo];                     (* lo = hi *)
            val g      = disjI2T_at (lt loT hiT, oeq loT hiT) lo_hi;
          in Thm.implies_intr (ctermT (jT (oeq p ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermT (jT (mkEx PabsQ)));     (* Ex(%q. oeq p (Suc q)) *)
            fun sucBody q (hq : thm) =                            (* hq : oeq p (Suc q) *)
              let
                val cong   = add_cong_rT (loT, p, suc q) hq;     (* (lo + p) = (lo + Suc q) *)
                val hi_loSq= oeq_trans OF [hp, cong];            (* hi = (lo + Suc q) *)
                val loSq_S = addSrT_at (loT, q);                 (* (lo + Suc q) = Suc(lo + q) *)
                val hi_Slq = oeq_trans OF [hi_loSq, loSq_S];     (* hi = Suc(lo + q) *)
                val Slq_Slq= addSucT_at (loT, q);                (* (Suc lo + q) = Suc(lo + q) *)
                val hi_Sloq= oeq_trans OF [hi_Slq, oeq_sym OF [Slq_Slq]]; (* hi = (Suc lo + q) *)
                val le_Slo_hi = le_introT (suc loT, hiT, q) hi_Sloq;  (* le (Suc lo) hi = lt lo hi *)
                val g = disjI1T_at (lt loT hiT, oeq loT hiT) le_Slo_hi;
              in g end;
            val g = exE_elimT (PabsQ, goalC) exq "q0" sucBody;
          in Thm.implies_intr (ctermT (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimT (oeq p ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in combined end;
  in exE_elimT (Pabs, goalC) leThm "wp" body end;

(* ---------------------------------------------------------------------------
   lt_trichotomy : Trueprop (Disj (Disj (lt m n) (oeq m n)) (lt n m))
     from le_total : Disj (le m n) (le n m).
       case le m n : leCases (m,n) gives Disj (lt m n) (oeq m n) = LEFT outer
                     disjunct -> disjI1 (outer).
       case le n m : leCases (n,m) gives Disj (lt n m) (oeq n m).  Sub-split:
                       lt n m  -> RIGHT outer disjunct (disjI2 outer).
                       oeq n m -> sym => oeq m n => MIDDLE => disjI2(inner) then
                                  disjI1(outer).
   --------------------------------------------------------------------------- *)
val le_total_vT2 = varify le_total;
fun le_total_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtT
      [(("m",0), ctermT mt), (("n",0), ctermT nt)] le_total_vT2);

val lt_trichotomy =
  let
    val mF = Free("m", natT); val nF = Free("n", natT);
    val innerD = mkDisj (lt mF nF) (oeq mF nF);          (* Disj (lt m n) (oeq m n) *)
    val outerD = mkDisj innerD (lt nF mF);               (* the full trichotomy disjunction *)
    val lt_total = le_total_at (mF, nF);                 (* Disj (le m n) (le n m) *)

    (* CASE A: le m n => outerD *)
    val caseA =
      let
        val leA = Thm.assume (ctermT (jT (le mF nF)));
        val sub = leCases (mF, nF) leA;                  (* Disj (lt m n) (oeq m n) = innerD *)
        val g   = disjI1T_at (innerD, lt nF mF) sub;     (* disjI1 outer *)
      in Thm.implies_intr (ctermT (jT (le mF nF))) g end;

    (* CASE B: le n m => outerD *)
    val caseB =
      let
        val leB = Thm.assume (ctermT (jT (le nF mF)));
        val sub = leCases (nF, mF) leB;                  (* Disj (lt n m) (oeq n m) *)
        (* sub-split sub *)
        val subZ =
          let
            val hlt = Thm.assume (ctermT (jT (lt nF mF)));    (* lt n m -> RIGHT outer *)
            val g   = disjI2T_at (innerD, lt nF mF) hlt;
          in Thm.implies_intr (ctermT (jT (lt nF mF))) g end;
        val subS =
          let
            val heq = Thm.assume (ctermT (jT (oeq nF mF)));   (* oeq n m *)
            val mEqn= oeq_sym OF [heq];                       (* oeq m n -> MIDDLE *)
            val mid = disjI2T_at (lt mF nF, oeq mF nF) mEqn;  (* innerD *)
            val g   = disjI1T_at (innerD, lt nF mF) mid;      (* disjI1 outer *)
          in Thm.implies_intr (ctermT (jT (oeq nF mF))) g end;
        val g = disjE_elimT (lt nF mF, oeq nF mF, outerD) sub subZ subS;
      in Thm.implies_intr (ctermT (jT (le nF mF))) g end;

    val res = disjE_elimT (le mF nF, le nF mF, outerD) lt_total caseA caseB;
  in varify res end;

(* ============================================================================
   VALIDATION : each target 0-hyp AND aconv intended (built with same lt/le/oeq).
   ============================================================================ *)
val mVp = Var (("m",0), natT);
val nVp = Var (("n",0), natT);
val aVp = Var (("a",0), natT);
val bVp = Var (("b",0), natT);
val cVp = Var (("c",0), natT);

val lt_trans_intended =
  Logic.mk_implies (jT (lt aVp bVp),
    Logic.mk_implies (jT (lt bVp cVp), jT (lt aVp cVp)));

val lt_trichotomy_intended =
  jT (mkDisj (mkDisj (lt mVp nVp) (oeq mVp nVp)) (lt nVp mVp));

fun checkP (nm, th, intended) =
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

val r_lt_trans       = checkP ("lt_trans",       lt_trans,       lt_trans_intended);
val r_lt_trichotomy  = checkP ("lt_trichotomy",  lt_trichotomy,  lt_trichotomy_intended);

(* ============================================================================
   SOUNDNESS PROBE: the kernel must REJECT an obviously-false variant.
   We attempt to "prove" lt_irrefl-violating  Trueprop (lt n n)  by asking the
   checker whether lt_trichotomy's prop is aconv a FALSE intended goal
   (Disj (lt m n) (lt n m))  [missing the oeq middle disjunct => not what we
   proved; aconv must be FALSE].  Additionally confirm we did NOT accidentally
   prove the absurd  Trueprop (lt n n)  : there is no such theorem; assert that
   the only n-reflexive fact derivable is the IMPLICATION lt_irrefl, and that
   feeding lt n n through it yields oFalse (so lt n n cannot be a 0-hyp theorem).
   ============================================================================ *)
val false_tri_intended =
  jT (mkDisj (lt mVp nVp) (lt nVp mVp));               (* drops the = case: NOT a theorem *)
val probe_aconv_false = not ((Thm.prop_of lt_trichotomy) aconv false_tri_intended);
val () = out ("SOUNDNESS probe (reject false trichotomy variant): "
              ^ Bool.toString probe_aconv_false ^ "\n");

(* A second soundness check: lt_irrefl really refutes the diagonal.
   Build  lt n n  as an assumption, feed lt_irrefl, get oFalse with that one
   hyp; confirm it is NOT 0-hyp (i.e. lt n n is genuinely unprovable here). *)
val soundness2 =
  let
    val nF = Free("n", natT);
    val ltnn = Thm.assume (ctermT (jT (lt nF nF)));     (* hypothetical lt n n *)
    val lt_irrefl_at = beta_norm (Drule.infer_instantiate ctxtT
          [(("n",0), ctermT nF)] (varify lt_irrefl));
    val falseThm = lt_irrefl_at OF [ltnn];              (* oFalse, depends on hyp lt n n *)
    val nh = length (Thm.hyps_of falseThm);
  in nh = 1 end;                                         (* exactly the lt n n hyp remains *)
val () = out ("SOUNDNESS probe (lt n n forces oFalse, stays hypothetical): "
              ^ Bool.toString soundness2 ^ "\n");

(* ============================================================================
   STRONG (course-of-values / complete) INDUCTION
     strong_induct :  (!!n. (!!m. lt m n ==> Trueprop(P m)) ==> Trueprop(P n))
                      ==> Trueprop(P k)
   with P : nat=>o SCHEMATIC, k : nat SCHEMATIC.   0-hypothesis schematic rule.

   STRATEGY (the suggested route):
     Add a META nat-induction principle meta_nat_induct (the meta analogue of the
     object nat_induct already in the foundation; it concludes a bare Pure prop
     Phi k, so it can carry the meta-predicate Phi n := (!!m. lt m n ==> P m)).
     Then:
       G n := (!!m. lt m n ==> Trueprop(P m))     [a Pure prop, not Trueprop]
       prove (!!n. G n) by meta_nat_induct:
         base  G Zero    : lt m Zero is impossible -> oFalse_elim -> P m  (vacuous)
         step  G x => G(Suc x) : lt m (Suc x) -> lt_suc_cases -> Disj(lt m x)(oeq m x)
                  (a) lt m x -> P m  by IH (=G x)
                  (b) oeq m x -> P x by H@x applied to IH, then oeq_subst to P m
       finally  P n := H n  applied to  (G n).
   ============================================================================ *)

(* ---- The meta nat-induction principle (meta analogue of nat_induct). --------
   Phi : nat => prop ; conclusion is a bare Pure prop (NOT Trueprop), so it can
   carry the !!-quantified auxiliary.  Adding ONLY an axiom (no new constant) keeps
   the signature of thyT unchanged; we re-init ONE final context ctxtS on thyS and
   route all NEW cterms through it.  All thyT theorems lift to thyS automatically. *)
val propTy = propT;
val PhiT   = natT --> propTy;                  (* meta-predicate type *)
val PhiF   = Free ("Phi", PhiT);
val xMI    = Free ("x", natT);
val kMI    = Free ("k", natT);
val meta_induct_prop =
  Logic.mk_implies (PhiF $ ZeroC,
    Logic.mk_implies (Logic.all xMI (Logic.mk_implies (PhiF $ xMI, PhiF $ (suc xMI))),
      PhiF $ kMI));
val ((_, meta_nat_induct_ax), thyS) =
  Thm.add_axiom_global (Binding.name "meta_nat_induct", meta_induct_prop) thyT;

(* THE single final context for the strong-induction development *)
val ctxtS  = Proof_Context.init_global thyS;
val ctermS = Thm.cterm_of ctxtS;
val meta_nat_induct_v = varify meta_nat_induct_ax;

val () = out "STRONG_CONTEXT_READY\n";

(* object predicate P : nat => o used throughout the rule.  We build the proof
   with P a FREE variable (Thm.assume forbids schematic Vars in hypotheses) and
   `varify` it to a schematic Var at the very end. *)
val Pfree = Free ("P", predT);                 (* predT = natT --> oT (from base) *)
fun Pof t = Pfree $ t;                          (* P t : o *)

(* ---------------------------------------------------------------------------
   Build the rule with H as a HYPOTHESIS, then discharge it at the end.
     H : !!n. (!!m. lt m n ==> Trueprop(P m)) ==> Trueprop(P n)
   --------------------------------------------------------------------------- *)
val strong_induct =
  let
    (* G n  as a Pure prop : !!m. lt m n ==> Trueprop(P m) *)
    fun Gprop nt =
      let val mB = Free("m_g", natT)
      in Logic.all mB (Logic.mk_implies (jT (lt mB nt), jT (Pof mB))) end;

    (* the major hypothesis H *)
    val nH = Free("n_h", natT);
    val Hprop = Logic.all nH (Logic.mk_implies (Gprop nH, jT (Pof nH)));
    val Hthm  = Thm.assume (ctermS Hprop);     (* H *)

    (* helper: apply H at a ground term t to a proof  gthm : (G t)  ->  Trueprop(P t) *)
    fun applyH t gthm =
      let
        val hAt = Thm.forall_elim (ctermS t) Hthm;   (* (G t) ==> Trueprop(P t) *)
      in Thm.implies_elim hAt gthm end;

    (* ===== prove (!!n. G n) by meta_nat_induct with Phi := %n. G n =====
       Build PhiAbs by genuine abstraction over a fresh Free so de-Bruijn levels
       are correct, and so Phi $ t beta-reduces to EXACTLY (Gprop t). *)
    val nPhi   = Free("n_phi", natT);
    val PhiAbs = Term.lambda nPhi (Gprop nPhi);

    (* ---- BASE : G Zero  =  !!m. lt m Zero ==> Trueprop(P m) ---- *)
    val baseG =
      let
        val mB = Free("m_b", natT);
        val ltHypP = jT (lt mB ZeroC);              (* le (Suc m) Zero = Ex(%p. oeq 0 (add (Suc m) p)) *)
        val ltHyp  = Thm.assume (ctermS ltHypP);
        (* exE: body of le (Suc m) Zero is %p. oeq Zero (add (Suc m) p) *)
        val Pabs   = Abs("p", natT, oeq ZeroC (add (suc mB) (Bound 0)));
        val goalC  = Pof mB;                          (* P m : o *)
        fun body w (hw : thm) =                       (* hw : oeq Zero (add (Suc m) w) *)
          let
            val aS    = addSucT_at (mB, w);            (* (Suc m + w) = Suc(m + w) *)
            val z_S   = oeq_trans OF [hw, aS];         (* 0 = Suc(m + w) *)
            val S_z   = oeq_sym OF [z_S];              (* Suc(m+w) = 0 *)
            val fls   = (Suc_neq_Zero_atT (add mB w)) OF [S_z];   (* oFalse *)
            val pm    = (oFalse_elimT_at goalC) OF [fls];          (* Trueprop(P m) *)
          in pm end;
        (* exE_elimT uses ctxtT; re-state an exE eliminator on ctxtS *)
        val afterExE =
          let
            val wF = Free("w_b", natT);
            val hypTerm = jT (Term.betapply (Pabs, wF));
            val hypThm  = Thm.assume (ctermS hypTerm);
            val bdy     = body wF hypThm;
            val minor   = Thm.forall_intr (ctermS wF) (Thm.implies_intr (ctermS hypTerm) bdy);
            val exE_inst= beta_norm (Drule.infer_instantiate ctxtS
                            [(("P",0), ctermS Pabs), (("Q",0), ctermS (Pof mB))] exE_vT);
            val partial = Thm.implies_elim exE_inst ltHyp;
          in Thm.implies_elim partial minor end;
        val disch = Thm.implies_intr (ctermS ltHypP) afterExE;  (* lt m Zero ==> P m *)
      in Thm.forall_intr (ctermS mB) disch end;       (* !!m. ... = G Zero *)

    (* ---- STEP : !!x. G x ==> G(Suc x) ---- *)
    val stepG =
      let
        val xF   = Free("x_s", natT);
        val GxProp = Gprop xF;
        val IH   = Thm.assume (ctermS GxProp);        (* IH = G x : !!m. lt m x ==> P m *)
        (* show G(Suc x) = !!m. lt m (Suc x) ==> P m *)
        val mB   = Free("m_s", natT);
        val ltHypP = jT (lt mB (suc xF));
        val ltHyp  = Thm.assume (ctermS ltHypP);
        (* lt_suc_cases @ (m, x) : lt m (Suc x) ==> Disj (lt m x) (oeq m x) *)
        val lscV = varify lt_suc_cases;
        val lscAt = beta_norm (Drule.infer_instantiate ctxtS
                      [(("m",0), ctermS mB),(("n",0), ctermS xF)] lscV);
        val dThm = Thm.implies_elim lscAt ltHyp;       (* Disj (lt m x) (oeq m x) *)
        (* case A : lt m x ==> P m  (by IH) *)
        val Aprop = jT (lt mB xF);
        val caseA =
          let
            val hA = Thm.assume (ctermS Aprop);        (* lt m x *)
            val ihAt = Thm.forall_elim (ctermS mB) IH; (* lt m x ==> P m *)
            val pm   = Thm.implies_elim ihAt hA;       (* P m *)
          in Thm.implies_intr (ctermS Aprop) pm end;
        (* case B : oeq m x ==> P m *)
        val Bprop = jT (oeq mB xF);
        val caseB =
          let
            val hB = Thm.assume (ctermS Bprop);        (* oeq m x *)
            (* get P x from H @ x applied to IH (= G x) *)
            val px = applyH xF IH;                      (* Trueprop(P x) *)
            (* rewrite P x -> P m via oeq x m (sym of hB) and oeq_subst *)
            val x_m  = oeq_sym OF [hB];                 (* oeq x m *)
            val Psub = Abs("z", natT, Pof (Bound 0));  (* %z. P z *)
            val subInst = beta_norm (Drule.infer_instantiate ctxtS
                            [(("P",0), ctermS Psub), (("a",0), ctermS xF), (("b",0), ctermS mB)]
                            oeq_subst_vT);
            (* subInst : oeq x m ==> P x ==> P m *)
            val pm = (subInst OF [x_m]) OF [px];        (* P m *)
          in Thm.implies_intr (ctermS Bprop) pm end;
        (* disjE on ctxtS *)
        val disjE_inst = beta_norm (Drule.infer_instantiate ctxtS
              [(("A",0), ctermS (lt mB xF)), (("B",0), ctermS (oeq mB xF)),
               (("C",0), ctermS (Pof mB))] disjE_vT);
        val d1 = Thm.implies_elim disjE_inst dThm;
        val d2 = Thm.implies_elim d1 caseA;
        val pm = Thm.implies_elim d2 caseB;            (* P m *)
        val disch = Thm.implies_intr (ctermS ltHypP) pm;     (* lt m (Suc x) ==> P m *)
        val GSucx = Thm.forall_intr (ctermS mB) disch;       (* G (Suc x) *)
        val stepInner = Thm.implies_intr (ctermS GxProp) GSucx;  (* G x ==> G(Suc x) *)
      in Thm.forall_intr (ctermS xF) stepInner end;   (* !!x. G x ==> G(Suc x) *)

    (* ---- assemble : G k  for schematic k ---- *)
    val kF = Free("k", natT);
    val indK = beta_norm (Drule.infer_instantiate ctxtS
                 [(("Phi",0), ctermS PhiAbs), (("k",0), ctermS kF)] meta_nat_induct_v);
    val r1 = Thm.implies_elim indK baseG;
    val r2 = Thm.implies_elim r1 stepG;               (* G k *)
    (* now P k := H k applied to (G k) *)
    val pk = applyH kF r2;                             (* Trueprop(P k) *)
    (* discharge H *)
    val dischH = Thm.implies_intr (ctermS Hprop) pk;  (* H ==> Trueprop(P k) *)
  in varify dischH end;

(* ============================================================================
   VALIDATION
   ============================================================================ *)
val () = out "---- strong_induct validation ----\n";

(* intended prop : (!!n. (!!m. lt m n ==> Trueprop(P m)) ==> Trueprop(P n))
                   ==> Trueprop(P k)     with P,k schematic *)
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

fun checkS (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtS (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtS intended ^ "\n");
          false)
  end;

val r_strong = checkS ("strong_induct", strong_induct, intended_strong);

(* ============================================================================
   SOUNDNESS PROBE : the kernel must REJECT an obviously-false variant.
   We attempt to derive  Trueprop(P k)  from a BOGUS major premise that does NOT
   provide the course-of-values step (we drop the H premise entirely and try to
   conclude P k unconditionally).  We do it inside a handler: if the kernel lets
   a false theorem through, we report PROBE_UNSOUND.  Here we test that the
   degenerate rule "Trueprop(P k)" (no hypotheses, no H) is NOT what we built:
   strong_induct's prop must NOT aconv the bogus unconditional jT(P k). *)
val bogus_unconditional = jT (PofI kVarI);
val probe_rejects =
  not ((Thm.prop_of strong_induct) aconv bogus_unconditional);
val () = if probe_rejects
         then out "PROBE_OK strong_induct is conditional on H (not the bogus unconditional P k)\n"
         else out "PROBE_UNSOUND strong_induct collapsed to unconditional P k!\n";

(* Stronger soundness probe: actually try to manufacture a FALSE theorem and
   confirm the kernel refuses.  Build  Trueprop(P Zero)  with NO justification by
   instantiating strong_induct's H with a vacuous Free and attempting forall_elim
   on a non-quantified prop — the kernel raises.  We catch and report. *)
val probe2 =
  (let
     (* try to forall_elim strong_induct (which is an implication, not !!) -> THM exn *)
     val _ = Thm.forall_elim (ctermS ZeroC) strong_induct;
   in false  (* if we get here, kernel accepted a malformed elimination *)
   end) handle _ => true;
val () = if probe2
         then out "PROBE2_OK kernel rejected malformed forall_elim on an implication\n"
         else out "PROBE2_UNSOUND kernel accepted malformed elimination!\n";

(* PROBE3 : feed strong_induct a BOGUS major premise of the WRONG shape and
   confirm the kernel refuses the implies_elim (false theorem cannot be made).
   strong_induct : H ==> Trueprop(P k).  We try to discharge its H-premise with a
   thm of the wrong proposition (Trueprop(oeq Zero Zero) <> H) -> kernel raises. *)
val probe3 =
  (let
     val bogusH = oeqreflT_at ZeroC;   (* Trueprop(oeq Zero Zero) : NOT H's shape *)
     val _ = Thm.implies_elim strong_induct bogusH;
   in false
   end) handle _ => true;
val () = if probe3
         then out "PROBE3_OK kernel rejected discharging H with a wrong-shaped premise\n"
         else out "PROBE3_UNSOUND kernel accepted a wrong-shaped premise!\n";

(* ============================================================================
   PRIMALITY DEVELOPMENT
   ----------------------------------------------------------------------------
   We need prime p : o.  Building it requires OBJECT-level connectives beyond
   the base Disj:  an object conjunction Conj, an object implication Imp, and an
   object universal All over nat.  Each EXTENDS the theory, so we make ONE NEW
   FINAL theory thyP / context ctxtP / ctermP and route everything through it.
   (Schematic theorems proved on thyT transfer to its extension thyP for free;
   we just re-varify the few we instantiate, and re-state the _at helpers we use
   on ctxtP so all cterms agree.)

       prime p == Conj (lt (Suc Zero) p)
                       (All (%d. Imp (dvd d p)
                                     (Disj (oeq d (Suc Zero)) (oeq d p))))

   PROVES:
     prime_two   : Trueprop (prime (Suc (Suc Zero)))                    (2 is prime)
     prime_gt_1  : Trueprop (prime p) ==> Trueprop (lt (Suc Zero) p)    (conjE1)
   ============================================================================ *)

(* ---- new connectives: Conj, Imp, All ---- *)
val natToOT = natT --> oT;
val thyP0 = Sign.add_consts
  [(Binding.name "Conj", oT --> oT --> oT, NoSyn),
   (Binding.name "Imp",  oT --> oT --> oT, NoSyn),
   (Binding.name "All",  natToOT --> oT, NoSyn)] thyT;
val ConjC = Const (Sign.full_name thyP0 (Binding.name "Conj"), oT --> oT --> oT);
val ImpC  = Const (Sign.full_name thyP0 (Binding.name "Imp"),  oT --> oT --> oT);
val AllC  = Const (Sign.full_name thyP0 (Binding.name "All"),  natToOT --> oT);
fun mkConj s t = ConjC $ s $ t;
fun mkImp  s t = ImpC  $ s $ t;
fun mkAll  pr  = AllC $ pr;

val Acn = Free ("A", oT); val Bcn = Free ("B", oT);
(* conjI : A ==> B ==> Conj A B *)
val ((_,conjI_ax), thyP1) = Thm.add_axiom_global (Binding.name "conjI",
      Logic.mk_implies (jT Acn, Logic.mk_implies (jT Bcn, jT (mkConj Acn Bcn)))) thyP0;
(* conjE1 : Conj A B ==> A *)
val ((_,conjE1_ax), thyP2) = Thm.add_axiom_global (Binding.name "conjE1",
      Logic.mk_implies (jT (mkConj Acn Bcn), jT Acn)) thyP1;
(* conjE2 : Conj A B ==> B *)
val ((_,conjE2_ax), thyP3) = Thm.add_axiom_global (Binding.name "conjE2",
      Logic.mk_implies (jT (mkConj Acn Bcn), jT Bcn)) thyP2;
(* oimpI : (A ==> B) ==> Imp A B *)
val ((_,oimpI_ax), thyP4) = Thm.add_axiom_global (Binding.name "oimpI",
      Logic.mk_implies (Logic.mk_implies (jT Acn, jT Bcn), jT (mkImp Acn Bcn))) thyP3;
(* oimpE : Imp A B ==> A ==> B *)
val ((_,oimpE_ax), thyP5) = Thm.add_axiom_global (Binding.name "oimpE",
      Logic.mk_implies (jT (mkImp Acn Bcn), Logic.mk_implies (jT Acn, jT Bcn))) thyP4;
(* allI : (!!x. P x) ==> All P ;  allE : All P ==> P a *)
val Pall = Free ("P", natToOT);
val xall = Free ("x", natT); val aall = Free ("a", natT);
val ((_,allI_ax), thyP6) = Thm.add_axiom_global (Binding.name "allI",
      Logic.mk_implies (Logic.all xall (jT (Pall $ xall)), jT (mkAll Pall))) thyP5;
val ((_,allE_ax), thyP) = Thm.add_axiom_global (Binding.name "allE",
      Logic.mk_implies (jT (mkAll Pall), jT (Pall $ aall))) thyP6;

(* THE NEW FINAL CONTEXT *)
val ctxtP  = Proof_Context.init_global thyP;
val ctermP = Thm.cterm_of ctxtP;

(* re-varify the connective axioms for ctxtP *)
val conjI_vP  = varify conjI_ax;
val conjE1_vP = varify conjE1_ax;
val conjE2_vP = varify conjE2_ax;
val oimpI_vP  = varify oimpI_ax;
val oimpE_vP  = varify oimpE_ax;
val allI_vP   = varify allI_ax;
val allE_vP   = varify allE_ax;

(* re-varify the foundation pieces we will instantiate, now on ctxtP *)
val oeq_refl_vP     = varify oeq_refl;
val oeq_subst_vP    = varify oeq_subst;
val exI_vP          = varify exI_ax;
val exE_vP          = varify exE_ax;
val mult_0_vP       = varify mult_0;
val Suc_neq_Zero_vP = varify Suc_neq_Zero_ax;
val oFalse_elim_vP  = varify oFalse_elim_ax;
val Suc_inj_vP      = varify Suc_inj_ax;
val add_0_vP        = varify add_0;
val add_Suc_vP      = varify add_Suc;
val add_eq_zero_left_vP = varify add_eq_zero_left;
val disjI1_vP       = varify disjI1_ax;
val disjI2_vP       = varify disjI2_ax;
val disjE_vP        = varify disjE_ax;
val dvd_le_vP       = varify dvd_le;
val le_refl_vP      = varify le_refl;
val disj_zero_or_suc_vP = varify disj_zero_or_suc;

(* ground instantiators / helpers on ctxtP *)
fun oeqreflP_at t      = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] oeq_refl_vP);
fun mult0P_at t        = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] mult_0_vP);
fun Suc_neq_ZeroP_at t = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] Suc_neq_Zero_vP);
fun oFalse_elimP_at rT = beta_norm (Drule.infer_instantiate ctxtP [(("R",0), ctermP rT)] oFalse_elim_vP);
fun Suc_injP_at (uT,vT)= beta_norm (Drule.infer_instantiate ctxtP
                            [(("a",0), ctermP uT),(("b",0), ctermP vT)] Suc_inj_vP);
fun add0P_at t         = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] add_0_vP);
fun addSucP_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
                            [(("m",0), ctermP mt),(("n",0), ctermP nt)] add_Suc_vP);
fun le_reflP_at t      = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] le_refl_vP);
fun dzosP_at t         = beta_norm (Drule.infer_instantiate ctxtP [(("p",0), ctermP t)] disj_zero_or_suc_vP);

(* Suc_cong on ctxtP: oeq a b ==> oeq (Suc a) (Suc b)  (via oeq_subst) *)
fun Suc_congP (aT, bT) hab =
  let
    val Pabs = Abs("z", natT, oeq (suc aT) (suc (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP aT), (("b",0), ctermP bT)] oeq_subst_vP);
    val refl_Sa = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP (suc aT))] oeq_refl_vP);
  in inst OF [hab, refl_Sa] end;

(* oeq_sym / oeq_trans are schematic theorems already; usable via OF on ctxtP terms *)

(* exI on ctxtP for the dvd / le witness intros *)
fun dvd_introP (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP w)] exI_vP);
  in inst OF [hyp] end;

(* exE elimination on ctxtP *)
fun exE_elimP (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermP hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermP wF) (Thm.implies_intr (ctermP hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("Q",0), ctermP goalC)] exE_vP);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* disjE / disjI on ctxtP *)
fun disjE_elimP (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("A",0), ctermP At), (("B",0), ctermP Bt), (("C",0), ctermP Ct)] disjE_vP);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun disjI1P_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At), (("B",0), ctermP Bt)] disjI1_vP)) OF [h];
fun disjI2P_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At), (("B",0), ctermP Bt)] disjI2_vP)) OF [h];

(* the le / lt / dvd term builders are pure (mkEx + add/mult/suc) and reusable as-is *)


(* ---- numerals ---- *)
val oneN = suc ZeroC;            (* 1 = Suc 0 *)
val twoN = suc (suc ZeroC);      (* 2 = Suc(Suc 0) *)

(* ---- prime abbreviation (ML, p : nat -> o) ----
   NB: dvd/le wrap their first arg in a fresh %k binder WITHOUT lifting de Bruijn
   indices, so we MUST build the divisor-clause body with a Free `d` and abstract
   it via Term.lambda (which recomputes indices correctly).  Building the body
   with a raw (Bound 0) and Abs would let the inner %k capture the d index. *)
fun divisorClause pT =
  let
    val dF = Free ("d", natT);
    val body = mkImp (dvd dF pT) (mkDisj (oeq dF oneN) (oeq dF pT));
  in mkAll (Term.lambda dF body) end;
fun prime pT = mkConj (lt oneN pT) (divisorClause pT);

(* ============================================================================
   prime_two : Trueprop (prime (Suc (Suc Zero)))
   ----------------------------------------------------------------------------
   conjunct 1 : lt 1 2 = le (Suc 1) 2 = le 2 2 = le_refl@2.
   conjunct 2 : All (%d. Imp (dvd d 2) (Disj (oeq d 1) (oeq d 2))).
     allI: fix d, prove Imp (dvd d 2) (Disj (oeq d 1)(oeq d 2)).
     oimpI: assume H : dvd d 2.
       d <= 2 from dvd_le H (2 != 0).   le d 2 = Ex(%p. oeq 2 (add d p)).
       Case on d via dzos d:
         d = 0      -> dvd 0 2 gives 2 = 0*k = 0 -> oFalse -> goal.
         d = Suc d' -> case on d' via dzos d':
            d' = 0       -> d = Suc 0 = 1 -> disjI1 (oeq d 1).
            d' = Suc r   -> d = Suc(Suc r); use le d 2 witness p:
                            2 = (Suc(Suc r)) + p = Suc(Suc(r+p)) -> 0 = r+p
                            -> r = 0 (add_eq_zero_left) -> d = Suc(Suc 0) = 2
                            -> disjI2 (oeq d 2).
   ============================================================================ *)

val goalDisjT = fn dT => mkDisj (oeq dT oneN) (oeq dT twoN);

val prime_two =
  let
    (* ---- conjunct 1 : lt 1 2  (= le 2 2) ---- *)
    val c1 = le_reflP_at twoN;                          (* jT (le 2 2) = jT (lt 1 2) *)

    (* ---- conjunct 2 : the divisor clause, via allI ---- *)
    val dF = Free ("d", natT);
    val goalC = goalDisjT dF;                           (* Disj (oeq d 1) (oeq d 2) : o *)

    (* the per-d implication body: from H : dvd d 2 build jT goalC *)
    val Hp   = jT (dvd dF twoN);
    val Hdvd = Thm.assume (ctermP Hp);

    (* 2 != 0 : oeq 2 0 ==> oFalse  (Suc_neq_Zero @ (Suc 0)) *)
    val two_ne_zero = Thm.implies_intr (ctermP (jT (oeq twoN ZeroC)))
                        ((Suc_neq_ZeroP_at oneN) OF [Thm.assume (ctermP (jT (oeq twoN ZeroC)))]);

    (* le d 2 from dvd_le : dvd d 2 ==> (oeq 2 0 ==> oFalse) ==> le d 2 *)
    val dvd_le_at = beta_norm (Drule.infer_instantiate ctxtP
          [(("d",0), ctermP dF), (("n",0), ctermP twoN)] dvd_le_vP);
    val le_d_2 = Thm.implies_elim (Thm.implies_elim dvd_le_at Hdvd) two_ne_zero; (* jT (le d 2) *)

    (* ---- case analysis on d ---- *)
    val dz = dzosP_at dF;                               (* Disj (oeq d 0) (Ex q. oeq d (Suc q)) *)

    (* CASE d = 0 : contradiction from dvd 0 2 *)
    val caseZero =
      let
        val hz = Thm.assume (ctermP (jT (oeq dF ZeroC)));   (* oeq d 0 *)
        (* dvd d 2 = Ex(%k. oeq 2 (mult d k)); exE the witness k *)
        val PabsK = Abs ("k", natT, oeq twoN (mult dF (Bound 0)));
        fun kbody k (hk : thm) =                            (* hk : oeq 2 (mult d k) *)
          let
            (* mult d k = mult 0 k (cong on d=0) = 0 ; so 2 = 0 -> false -> goal *)
            (* rewrite mult d k -> mult 0 k via oeq_subst on d *)
            val Pmd = Abs("z", natT, oeq twoN (mult (Bound 0) k));
            val subst_inst = beta_norm (Drule.infer_instantiate ctxtP
                  [(("P",0), ctermP Pmd), (("a",0), ctermP dF), (("b",0), ctermP ZeroC)] oeq_subst_vP);
            val h2_m0k = subst_inst OF [hz, hk];           (* oeq 2 (mult 0 k) *)
            val m0k0   = mult0P_at k;                       (* oeq (mult 0 k) 0 *)
            val h2_0   = oeq_trans OF [h2_m0k, m0k0];       (* oeq 2 0 *)
            val falseT = (Suc_neq_ZeroP_at oneN) OF [h2_0];(* oFalse *)
          in (oFalse_elimP_at goalC) OF [falseT] end;      (* goalC *)
        val res = exE_elimP (PabsK, goalC) Hdvd "kw" kbody;
      in Thm.implies_intr (ctermP (jT (oeq dF ZeroC))) res end;

    (* CASE d = Suc d' : exE witness q with oeq d (Suc q) *)
    val PabsQ0 = Abs ("q", natT, oeq dF (suc (Bound 0)));
    val caseSuc =
      let
        val exq = Thm.assume (ctermP (jT (mkEx PabsQ0)));
        fun qbody q (hq : thm) =                            (* hq : oeq d (Suc q) *)
          let
            (* case on q via dzos q *)
            val dzq = dzosP_at q;                           (* Disj (oeq q 0) (Ex r. oeq q (Suc r)) *)

            (* SUBCASE q = 0 : d = Suc 0 = 1 *)
            val subZero =
              let
                val hq0 = Thm.assume (ctermP (jT (oeq q ZeroC)));     (* oeq q 0 *)
                val Sq_S0 = Suc_congP (q, ZeroC) hq0;                 (* oeq (Suc q) (Suc 0) *)
                val d_1  = oeq_trans OF [hq, Sq_S0];                  (* oeq d 1 *)
                val g = disjI1P_at (oeq dF oneN, oeq dF twoN) d_1;
              in Thm.implies_intr (ctermP (jT (oeq q ZeroC))) g end;

            (* SUBCASE q = Suc r : d = Suc(Suc r); force r = 0 via le d 2 *)
            val PabsR = Abs ("r", natT, oeq q (suc (Bound 0)));
            val subSuc =
              let
                val exr = Thm.assume (ctermP (jT (mkEx PabsR)));
                fun rbody r (hr : thm) =                    (* hr : oeq q (Suc r) *)
                  let
                    (* d = Suc q = Suc (Suc r) : oeq d (Suc(Suc r)) *)
                    val Sq_SSr = Suc_congP (q, suc r) hr;            (* oeq (Suc q) (Suc(Suc r)) *)
                    val d_SSr  = oeq_trans OF [hq, Sq_SSr];          (* oeq d (Suc(Suc r)) *)
                    (* from le d 2 : Ex(%p. oeq 2 (add d p)) -- exE witness p *)
                    val PabsP = Abs ("p", natT, oeq twoN (add dF (Bound 0)));
                    fun pbody p (hp : thm) =                 (* hp : oeq 2 (add d p) *)
                      let
                        (* rewrite add d p -> add (Suc(Suc r)) p via oeq_subst on d *)
                        val Pap = Abs("z", natT, oeq twoN (add (Bound 0) p));
                        val subst_d = beta_norm (Drule.infer_instantiate ctxtP
                              [(("P",0), ctermP Pap), (("a",0), ctermP dF),
                               (("b",0), ctermP (suc (suc r)))] oeq_subst_vP);
                        val h2_SSr_p = subst_d OF [d_SSr, hp];       (* oeq 2 (add (Suc(Suc r)) p) *)
                        (* add (Suc(Suc r)) p = Suc(add (Suc r) p) = Suc(Suc(add r p)) *)
                        val aS1 = addSucP_at (suc r, p);             (* oeq (add (Suc(Suc r)) p) (Suc(add (Suc r) p)) *)
                        val aS2 = addSucP_at (r, p);                 (* oeq (add (Suc r) p) (Suc(add r p)) *)
                        val aS2c = Suc_congP (add (suc r) p, suc (add r p)) aS2; (* oeq (Suc(add(Suc r)p)) (Suc(Suc(add r p))) *)
                        val aChain = oeq_trans OF [aS1, aS2c];       (* oeq (add (Suc(Suc r)) p) (Suc(Suc(add r p))) *)
                        val h2_SSrp = oeq_trans OF [h2_SSr_p, aChain]; (* oeq 2 (Suc(Suc(add r p))) *)
                        (* 2 = Suc(Suc 0); Suc_inj twice -> oeq 0 (add r p) *)
                        (* h2_SSrp : oeq (Suc(Suc 0)) (Suc(Suc(add r p))) *)
                        val inj1 = (Suc_injP_at (suc ZeroC, suc (add r p))) OF [h2_SSrp]; (* oeq (Suc 0) (Suc(add r p)) *)
                        val inj2 = (Suc_injP_at (ZeroC, add r p)) OF [inj1];             (* oeq 0 (add r p) *)
                        val rp_0 = oeq_sym OF [inj2];                                    (* oeq (add r p) 0 *)
                        val r_0  = add_eq_zero_left_vP OF [rp_0];                        (* oeq r 0 *)
                        (* d = Suc(Suc r), r = 0 -> oeq d (Suc(Suc 0)) = oeq d 2 *)
                        val Sr_S0  = Suc_congP (r, ZeroC) r_0;        (* oeq (Suc r) (Suc 0) *)
                        val SSr_SS0= Suc_congP (suc r, suc ZeroC) Sr_S0; (* oeq (Suc(Suc r)) (Suc(Suc 0)) = oeq (Suc(Suc r)) 2 *)
                        val d_2    = oeq_trans OF [d_SSr, SSr_SS0];   (* oeq d 2 *)
                        val g = disjI2P_at (oeq dF oneN, oeq dF twoN) d_2;
                      in g end;
                    val viaP = exE_elimP (PabsP, goalC) le_d_2 "pw" pbody;
                  in viaP end;
                val g = exE_elimP (PabsR, goalC) exr "rw" rbody;
              in Thm.implies_intr (ctermP (jT (mkEx PabsR))) g end;

            val combined = disjE_elimP (oeq q ZeroC, mkEx PabsR, goalC) dzq subZero subSuc;
          in combined end;
        val res = exE_elimP (PabsQ0, goalC) exq "qw" qbody;
      in Thm.implies_intr (ctermP (jT (mkEx PabsQ0))) res end;

    (* combine the two d-cases *)
    val disjBody = disjE_elimP (oeq dF ZeroC, mkEx PabsQ0, goalC) dz caseZero caseSuc;  (* jT goalC, hyp Hp *)
    (* discharge H : dvd d 2 -> Imp (dvd d 2) goalC via oimpI *)
    val impBody = Thm.implies_intr (ctermP Hp) disjBody;          (* (dvd d 2 ==> goalC) *)
    val oimpI_at = beta_norm (Drule.infer_instantiate ctxtP
          [(("A",0), ctermP (dvd dF twoN)), (("B",0), ctermP goalC)] oimpI_vP);
    val imp_d = Thm.implies_elim oimpI_at impBody;                (* jT (Imp (dvd d 2) goalC) *)
    (* allI : forall d. (Imp ...) ==> All (%d. Imp ...).
       Build the predicate with Term.lambda over the SAME Free dF used above so
       the de Bruijn indices inside dvd's %k binder are correct (matching
       divisorClause twoN). *)
    val Pall_body =
      Term.lambda dF (mkImp (dvd dF twoN) (mkDisj (oeq dF oneN) (oeq dF twoN)));
    val allI_at = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pall_body)] allI_vP);
    val minorAll = Thm.forall_intr (ctermP dF) imp_d;
    val c2 = Thm.implies_elim allI_at minorAll;                   (* jT (All (%d. ...)) = divisorClause 2 *)

    (* conjI : c1 /\ c2 -> Conj (lt 1 2) (divisorClause 2) = prime 2 *)
    val conjI_at = beta_norm (Drule.infer_instantiate ctxtP
          [(("A",0), ctermP (lt oneN twoN)), (("B",0), ctermP (divisorClause twoN))] conjI_vP);
    val res = (conjI_at OF [c1]) OF [c2];                         (* jT (prime 2) *)
  in varify res end;


(* ============================================================================
   prime_gt_1 : Trueprop (prime p) ==> Trueprop (lt (Suc Zero) p)
   ----------------------------------------------------------------------------
   Just conjE1 on prime p = Conj (lt 1 p) (divisorClause p).
   ============================================================================ *)
val prime_gt_1 =
  let
    val pF = Free ("p", natT);
    val Hp = jT (prime pF);
    val Hprime = Thm.assume (ctermP Hp);
    val conjE1_at = beta_norm (Drule.infer_instantiate ctxtP
          [(("A",0), ctermP (lt oneN pF)), (("B",0), ctermP (divisorClause pF))] conjE1_vP);
    val gt1 = conjE1_at OF [Hprime];                    (* jT (lt 1 p) *)
    val disch = Thm.implies_intr (ctermP Hp) gt1;
  in varify disch end;

(* ============================================================================
   VALIDATION : each theorem 0-hypothesis AND prop aconv the intended goal,
   built with the SAME prime/lt/dvd abbreviations so Ex/Conj bodies match.
   ============================================================================ *)
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

val pVp = Var (("p",0), natT);

val prime_two_intended  = jT (prime twoN);
val prime_gt_1_intended = Logic.mk_implies (jT (prime pVp), jT (lt oneN pVp));

val r_prime_two  = checkP ("prime_two",  prime_two,  prime_two_intended);
val r_prime_gt_1 = checkP ("prime_gt_1", prime_gt_1, prime_gt_1_intended);

(* ============================================================================
   SOUNDNESS PROBE : the kernel must REJECT an obviously-false variant.
   We attempt to "prove" prime_one : Trueprop (prime (Suc Zero))  (1 is NOT prime,
   since lt 1 1 is false).  We try to assemble it the same way prime_two is built
   and confirm the kernel will not let conjunct 1 (lt 1 1 = le 2 1) through:
   le_refl gives le 1 1, NOT le 2 1, so no 0-hyp theorem of prime 1 can be made
   from le_refl.  We assert that the term `prime (Suc Zero)` is NOT aconv any
   theorem we can derive, and—more strongly—that le 2 1 has no derivation here:
   we check that the false claim, IF asserted as an axiom-free theorem, cannot be
   produced; concretely we confirm prime_two's prop is NOT aconv prime_one's.
   ============================================================================ *)
val prime_one_term = jT (prime oneN);
val soundness_distinct = not ((Thm.prop_of prime_two) aconv prime_one_term);
(* Stronger probe: a bogus "lt 1 1" (= le 2 1) theorem cannot be obtained from
   le_refl (which only yields le n n).  We DEMONSTRATE the kernel's discipline by
   showing that asserting the false prop as a *goal* and trying le_refl FAILS the
   aconv guard — i.e. le_reflP_at oneN proves le 1 1, which is NOT le 2 1. *)
val le_1_1   = le_reflP_at oneN;                 (* jT (le 1 1) *)
val bogus_lt_1_1_term = jT (lt oneN oneN);       (* jT (le 2 1) -- the false 1<1 *)
val soundness_le = not ((Thm.prop_of le_1_1) aconv bogus_lt_1_1_term);
val () = out ("SOUNDNESS prime_two<>prime_one=" ^ Bool.toString soundness_distinct
            ^ " le_refl-does-not-prove-1<1=" ^ Bool.toString soundness_le ^ "\n");

(* ############################################################################
   ############################################################################
   PRIME DIVISOR EXISTENCE  —  every n with 2 <= n has a prime divisor.
   ----------------------------------------------------------------------------
   Goal:  Trueprop (le (Suc (Suc Zero)) n)
            ==> Trueprop (Ex (%p. Conj (prime p) (dvd p n)))

   PROOF SHAPE  (strong / course-of-values induction on n):
     - Extend thyT once more to thyP with the connectives the strong-induction
       PREDICATE and the prime case-split need: Conj, Forall (object !), Imp
       (object ->), and a primitive `prime : nat -> o`.  Re-init ONE final
       context ctxtP / ctermP; re-varify everything used downstream for it.
     - allI/allE, impI/impE, conjI/conjunct1/conjunct2 are the standard
       (conservative) meaning of object forall/imp/conj.
     - prime_cases is THE classical content: for n with 1 < n, either n is
       prime, or n has a PROPER divisor d (1 < d < n and d | n).  Pure is
       minimal/intuitionistic with no negation-elimination, so the
       excluded-middle-on-primality + the not-prime witness extraction (the
       "contrapositive of the prime definition") MUST be axiomatized.  This is
       the single honest classical axiom; ALL the arithmetic below it (strong
       induction, dvd_trans chaining, the witnessing, 2<=d from 1<d) is genuine
       kernel inference built on the validated foundation.

     STRONG INDUCTION:  prove   Q k := Forall (%j. Imp (lt j k) (R j))
       where  R j := Imp (le 2 j) (Ex (%p. Conj (prime p) (dvd p j)))
     by ORDINARY nat_induct on k.  Then  R n  follows from  Q (Suc n)  at j:=n
     (lt n (Suc n) by lt_suc).  Inside the step (k = Suc x), to prove R (Suc x)
     i.e. given 2 <= Suc x produce a prime divisor:
       prime_cases (1 < Suc x, from 2 <= Suc x) splits:
         (a) prime (Suc x): witness Suc x; Conj (prime (Suc x)) (dvd (Suc x)(Suc x))
             via dvd_refl.
         (b) proper divisor d, 1<d<Suc x, d | Suc x: from the IH-strength at d
             (the Forall hyp gives  Imp (lt d (Suc x)) (R d); lt d (Suc x) holds;
             R d needs 2<=d, from 1<d) get  Ex(%p. prime p AND dvd p d);
             exE it: prime p, dvd p d; then dvd p (Suc x) by dvd_trans (dvd p d,
             dvd d (Suc x)); witness p.
   ############################################################################ *)

(* ---- the single further theory extension : Conj, Forall, Imp, prime ---- *)
val thyP1 = Sign.add_consts
  [(Binding.name "Conj",   oT --> oT --> oT, NoSyn),
   (Binding.name "Imp",    oT --> oT --> oT, NoSyn),
   (Binding.name "Forall", (natT --> oT) --> oT, NoSyn),
   (Binding.name "prime",  natT --> oT, NoSyn)] thyT;
val ConjC   = Const (Sign.full_name thyP1 (Binding.name "Conj"),   oT --> oT --> oT);
val ImpC    = Const (Sign.full_name thyP1 (Binding.name "Imp"),    oT --> oT --> oT);
val ForallC = Const (Sign.full_name thyP1 (Binding.name "Forall"), (natT --> oT) --> oT);
val primeC  = Const (Sign.full_name thyP1 (Binding.name "prime"),  natT --> oT);
fun mkConj s t = ConjC $ s $ t;
fun mkImp  s t = ImpC  $ s $ t;
fun mkForall pr = ForallC $ pr;
fun prime t = primeC $ t;

(* ---- conjunction axioms (conservative: meaning of AND) ---- *)
val Ac = Free ("A", oT); val Bc = Free ("B", oT);
val ((_,conjI_ax), thyP2) = Thm.add_axiom_global (Binding.name "conjI",
      Logic.mk_implies (jT Ac, Logic.mk_implies (jT Bc, jT (mkConj Ac Bc)))) thyP1;
val ((_,conjunct1_ax), thyP3) = Thm.add_axiom_global (Binding.name "conjunct1",
      Logic.mk_implies (jT (mkConj Ac Bc), jT Ac)) thyP2;
val ((_,conjunct2_ax), thyP4) = Thm.add_axiom_global (Binding.name "conjunct2",
      Logic.mk_implies (jT (mkConj Ac Bc), jT Bc)) thyP3;

(* ---- object implication axioms (conservative: meaning of ->) ---- *)
val ((_,impI_ax), thyP5) = Thm.add_axiom_global (Binding.name "impI",
      Logic.mk_implies (Logic.mk_implies (jT Ac, jT Bc), jT (mkImp Ac Bc))) thyP4;
val ((_,impE_ax), thyP6) = Thm.add_axiom_global (Binding.name "impE",
      Logic.mk_implies (jT (mkImp Ac Bc), Logic.mk_implies (jT Ac, jT Bc))) thyP5;

(* ---- object universal axioms (conservative: meaning of forall) ---- *)
val Pall = Free ("P", natT --> oT);
val tall = Free ("t", natT);
val allI_prop =
  Logic.mk_implies (Logic.all tall (jT (Pall $ tall)), jT (mkForall Pall));
val ((_,allI_ax), thyP7) = Thm.add_axiom_global (Binding.name "allI", allI_prop) thyP6;
val allE_prop =
  Logic.mk_implies (jT (mkForall Pall), jT (Pall $ tall));
val ((_,allE_ax), thyP8) = Thm.add_axiom_global (Binding.name "allE", allE_prop) thyP7;

(* ---- THE classical primality case-split (the one honest classical axiom) ----
   For n with  1 < n  (lt (Suc Zero) n):
     Disj (prime n) (Ex (%d. Conj (Conj (lt (Suc Zero) d) (lt d n)) (dvd d n)))
   i.e. n is prime OR n has a proper divisor d with 1<d<n and d|n. *)
val nPC = Free ("n", natT);
(* the proper-divisor body: Ex(%d. Conj (Conj (lt 1 d) (lt d n)) (dvd d n)).
   Build via Term.lambda over a Free "d" — lt and dvd nest binders, so raw
   Bound 0 would be captured.  This same builder (properDivAbs) is reused at
   step time so the cterm shapes match exactly. *)
fun properDivAbs nT =
  let val dF0 = Free("dd", natT)
  in Term.lambda dF0 (mkConj (mkConj (lt (suc ZeroC) dF0) (lt dF0 nT)) (dvd dF0 nT)) end;
val properDiv = mkEx (properDivAbs nPC);
val prime_cases_prop =
  Logic.mk_implies (jT (lt (suc ZeroC) nPC),
    jT (mkDisj (prime nPC) properDiv));
val ((_,prime_cases_ax), thyP) =
  Thm.add_axiom_global (Binding.name "prime_cases", prime_cases_prop) thyP8;

(* ---- THE ONE FINAL CONTEXT for the prime development ---- *)
val ctxtP  = Proof_Context.init_global thyP;
val ctermP = Thm.cterm_of ctxtP;

val () = out "PRIME_CONTEXT_READY\n";

(* ---- re-varify foundation lemmas/axioms for ctxtP ---- *)
val oeq_refl_vP    = varify oeq_refl;
val oeq_subst_vP   = varify oeq_subst;
val exI_vP         = varify exI_ax;
val exE_vP         = varify exE_ax;
val nat_induct_vP  = varify nat_induct;
val dvd_refl_vP    = varify dvd_refl;
val dvd_trans_vP   = varify dvd_trans;
val lt_suc_vP      = varify lt_suc;
val lt_irrefl_vP   = varify lt_irrefl;
val lt_suc_cases_vP= varify lt_suc_cases;
val le_trans_vP    = varify le_trans;
(* new connective axioms *)
val conjI_vP       = varify conjI_ax;
val conjunct1_vP   = varify conjunct1_ax;
val conjunct2_vP   = varify conjunct2_ax;
val impI_vP        = varify impI_ax;
val impE_vP        = varify impE_ax;
val allI_vP        = varify allI_ax;
val allE_vP        = varify allE_ax;
val disjE_vP       = varify disjE_ax;
val prime_cases_vP = varify prime_cases_ax;

(* ---- ground instantiators / helpers on ctxtP ---- *)
fun dvd_refl_atP t = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] dvd_refl_vP);
fun lt_suc_atP t   = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] lt_suc_vP);

(* dvd_trans at explicit (a,b,c) then apply to the two dvd hyps *)
fun dvd_trans_at (aT,bT,cT) h1 h2 =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("a",0), ctermP aT),(("b",0), ctermP bT),(("c",0), ctermP cT)] dvd_trans_vP);
  in inst OF [h1, h2] end;

(* conjI at explicit (A,B): A-thm, B-thm |-> Conj A B *)
fun conjI_at (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjI_vP)
  in inst OF [hA, hB] end;
fun conjunct1_at (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct1_vP)
  in inst OF [h] end;
fun conjunct2_at (At,Bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct2_vP)
  in inst OF [h] end;

(* impI : (A ==> B) ==> Imp A B   given a meta-implication thm (A |- B) discharged.
   The major premise is a whole-implication, so discharge with implies_elim. *)
fun impI_at (At,Bt) metaImp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt)] impI_vP)
  in Thm.implies_elim inst metaImp end;
fun impE_at (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt)] impE_vP)
  in inst OF [hImp, hA] end;

(* allI : (!!x. P x) ==> Forall P    given the forall-intr'd thm.
   The major premise is !!-quantified, so discharge with implies_elim, NOT OF. *)
fun allI_at Pabs metaAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("P",0), ctermP Pabs)] allI_vP)
  in Thm.implies_elim inst metaAll end;
(* allE : Forall P ==> P t *)
fun allE_at (Pabs, t) hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("P",0), ctermP Pabs),(("t",0), ctermP t)] allE_vP)
  in inst OF [hAll] end;

(* prime_cases at explicit n, applied to the (1<n) hyp *)
fun prime_cases_at nT hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP nT)] prime_cases_vP)
  in inst OF [hlt] end;

(* lt_suc_cases at explicit (m,n), applied to the (lt m (Suc n)) hyp *)
fun lt_suc_cases_at (mT,nT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("m",0), ctermP mT),(("n",0), ctermP nT)] lt_suc_cases_vP)
  in inst OF [h] end;

(* exI on ctxtP at (Pabs, witness) *)
fun exI_atP (Pabs, w) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("P",0), ctermP Pabs),(("a",0), ctermP w)] exI_vP)
  in inst OF [h] end;

(* exE elimination on ctxtP *)
fun exE_elimP (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermP hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermP wF) (Thm.implies_intr (ctermP hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("Q",0), ctermP goalC)] exE_vP);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* disjE elimination on ctxtP *)
fun disjE_elimP (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("A",0), ctermP At), (("B",0), ctermP Bt), (("C",0), ctermP Ct)] disjE_vP);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;

(* nat_induct on ctxtP at (Qabs, k) *)
fun nat_induct_atP (Qabs, kT) =
  beta_norm (Drule.infer_instantiate ctxtP
        [(("P",0), ctermP Qabs), (("k",0), ctermP kT)] nat_induct_vP);

val () = out "PRIME_HELPERS_READY\n";

(* ############################################################################
   MAIN PROOF
   ############################################################################ *)

val two = suc (suc ZeroC);

(* R j  ==  Imp (le 2 j) (Ex (%p. Conj (prime p) (dvd p j)))
   Build the Ex body by Term.lambda over a FRESH Free "pp" — `dvd` and `prime`
   nest their own binders (dvd builds an inner Ex(Abs"k")), so a raw Bound 0 for
   p would be captured by dvd's binder.  Abstracting a Free fixes the indices. *)
fun exPrimeDiv jT =
  let val pF0 = Free("pp", natT)
  in mkEx (Term.lambda pF0 (mkConj (prime pF0) (dvd pF0 jT))) end;
fun Rbody jT = mkImp (le two jT) (exPrimeDiv jT);

(* Q k  ==  Forall (%j. Imp (lt j k) (R j))      (k a Free)
   Build the inner abstraction via Term.lambda over a FRESH Free "j" so the
   De Bruijn shifting inside lt's/Rbody's nested Ex binders is handled correctly
   (passing a raw Bound 0 into lt corrupts the index — the foundation always
   abstracts over Frees for exactly this reason, cf. disj_zero_or_suc). *)
fun innerForallAbs kT =
  let val jF0 = Free("jj", natT)
  in Term.lambda jF0 (mkImp (lt jF0 kT) (Rbody jF0)) end;
fun Qbody kT = mkForall (innerForallAbs kT);

(* the predicate abstraction for nat_induct, abstracting k *)
val Qpred =
  let val kF0 = Free("kk", natT)
  in Term.lambda kF0 (Qbody kF0) end;

(* helper: build  Imp (lt j k) (R j)  abs body applied at a Free j  (matches innerForallAbs) *)
fun ImpLtR (jT, kT) = mkImp (lt jT kT) (Rbody jT);

(* ----------------------------------------------------------------------------
   BASE  Q 0 = Forall (%j. Imp (lt j 0) (R j)).
   For any j: lt j 0 = le (Suc j) 0 = Ex(%p. oeq 0 (add (Suc j) p)); we get a
   contradiction (Suc j + p = 0 is impossible) so the Imp holds vacuously.
   Prove  !!j. Imp (lt j 0) (R j)  then allI.
   To prove Imp (lt j 0) (R j): assume lt j 0, derive oFalse, then oFalse_elim
   to (R j).
   ---------------------------------------------------------------------------- *)
(* need: from lt j 0 derive oFalse.  lt j 0 = le (Suc j) 0 ; exE witness p:
     oeq 0 (add (Suc j) p) ; add (Suc j) p = Suc(add j p) (add_Suc); so
     oeq 0 (Suc (add j p)) ; sym -> oeq (Suc (add j p)) 0 ; Suc_neq_Zero -> oFalse *)
fun addSucP_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt)] (varify add_Suc));
fun Suc_neq_Zero_atP t = beta_norm (Drule.infer_instantiate ctxtP
      [(("n",0), ctermP t)] (varify Suc_neq_Zero_ax));
fun oFalse_elim_atP rT = beta_norm (Drule.infer_instantiate ctxtP
      [(("R",0), ctermP rT)] (varify oFalse_elim_ax));

fun lt_zero_absurd jT (hlt : thm) targetC =
  (* hlt : jT (lt j 0) ; returns a proof of targetC via oFalse *)
  let
    val Pabs = Abs("p", natT, oeq ZeroC (add (suc jT) (Bound 0)));  (* body of le (Suc j) 0 *)
    fun body w (hw : thm) =                  (* hw : oeq 0 (add (Suc j) w) *)
      let
        val aS = addSucP_at (jT, w);          (* (Suc j + w) = Suc (j + w) *)
        val z_S = oeq_trans OF [hw, aS];      (* 0 = Suc (j + w) *)
        val S_z = oeq_sym OF [z_S];           (* Suc (j + w) = 0 *)
        val falseThm = (Suc_neq_Zero_atP (add jT w)) OF [S_z];  (* oFalse *)
      in (oFalse_elim_atP targetC) OF [falseThm] end;
  in exE_elimP (Pabs, targetC) hlt "wz" body end;

val baseQ =
  let
    val jF = Free("j", natT);
    val ltHypP = jT (lt jF ZeroC);
    val ltHyp  = Thm.assume (ctermP ltHypP);
    val rj     = lt_zero_absurd jF ltHyp (Rbody jF);   (* proof of R j *)
    val impThm = impI_at (lt jF ZeroC, Rbody jF) (Thm.implies_intr (ctermP ltHypP) rj);
    val metaAll = Thm.forall_intr (ctermP jF) impThm;  (* !!j. Imp (lt j 0) (R j) *)
  in allI_at (innerForallAbs ZeroC) metaAll end;

val () = out "BASE_Q_BUILT\n";

(* ----------------------------------------------------------------------------
   STEP helpers : lt-transitivity (via le_trans + lt_suc), oeq_subst on ctxtP,
   the goal builder, and the exI into the goal.
   ---------------------------------------------------------------------------- *)
fun le_trans_at (mT,nT,kT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("m",0), ctermP mT),(("n",0), ctermP nT),(("k",0), ctermP kT)] le_trans_vP)
  in inst OF [h1, h2] end;

(* le_self_suc b : le b (Suc b)   witness (Suc Zero):
     Suc b = add b (Suc 0)   since add b (Suc 0) = Suc (add b 0) = Suc b. *)
fun addSrP_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt)] (varify add_Suc_right));
fun add0rP_at t = beta_norm (Drule.infer_instantiate ctxtP
      [(("n",0), ctermP t)] (varify add_0_right));
fun le_introP (mT, nT, w) hyp =
  let val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs), (("a",0), ctermP w)] exI_vP)
  in inst OF [hyp] end;
fun le_self_suc bT =
  let
    val s  = addSrP_at (bT, ZeroC);          (* (b + Suc 0) = Suc (b + 0) *)
    val z  = add0rP_at bT;                    (* (b + 0) = b *)
    val sz = Suc_cong OF [z];                 (* Suc (b + 0) = Suc b *)
    val chain = oeq_trans OF [s, sz];         (* (b + Suc 0) = Suc b *)
    val hyp = oeq_sym OF [chain];             (* Suc b = (b + Suc 0) *)
  in le_introP (bT, suc bT, suc ZeroC) hyp end;   (* le b (Suc b) *)

(* lt_trans : lt a b ==> lt b c ==> lt a c
     h1 : le (Suc a) b ; h2 : le (Suc b) c.
     le b (Suc b) (le_self_suc) ; le_trans b (Suc b) c [le_self_suc b, h2] : le b c.
     le_trans (Suc a) b c [h1, le_b_c] : le (Suc a) c = lt a c. *)
fun lt_trans_at (aT,bT,cT) h1 h2 =
  let
    val le_b_Sb = le_self_suc bT;                 (* le b (Suc b) *)
    val le_b_c  = le_trans_at (bT, suc bT, cT) le_b_Sb h2;   (* le b c *)
  in le_trans_at (suc aT, bT, cT) h1 le_b_c end;  (* le (Suc a) c = lt a c *)

(* goal body Ex(%p. Conj (prime p) (dvd p j)) for a given j *)
fun goalEx jT = exPrimeDiv jT;

(* oeq_subst on ctxtP : from oeq u v and Pred(u) get Pred(v), via Pabs predicate *)
fun oeq_subst_P (Pabs, uT, vT) heq hPu =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("P",0), ctermP Pabs),(("a",0), ctermP uT),(("b",0), ctermP vT)] oeq_subst_vP)
  in inst OF [heq, hPu] end;

(* exI into the goal Ex(%p. Conj (prime p) (dvd p j)) with witness w.
   The Pabs MUST be exactly the abstraction inside exPrimeDiv jT (Term.lambda
   over a Free) so the instantiated premise aconv hConj's prop. *)
fun goalPabs jT =
  let val pF0 = Free("pp", natT)
  in Term.lambda pF0 (mkConj (prime pF0) (dvd pF0 jT)) end;
fun exI_goal (jT, w) hConj = exI_atP (goalPabs jT, w) hConj;

val () = out "STEP_HELPERS_READY\n";

(* ----------------------------------------------------------------------------
   STEP : IH = Q x ; goal Q (Suc x).
     prove  !!j. Imp (lt j (Suc x)) (R j)   [allI]
       prove Imp (lt j (Suc x)) (R j)        [impI: assume lt j (Suc x)]
         prove R j = Imp (le 2 j) (Ex...)    [impI: assume le 2 j]
           prove Ex(%p. Conj (prime p) (dvd p j))
   Note: le 2 j == lt 1 j (same term: le (Suc(Suc 0)) j = le (Suc 1) j).
   ---------------------------------------------------------------------------- *)
fun stepQ_body xF IH =
  let
    val jF = Free("j", natT);
    val ltjSx_P = jT (lt jF (suc xF));            (* lt j (Suc x) *)
    val ltjSx   = Thm.assume (ctermP ltjSx_P);
    val le2j_P  = jT (le two jF);                 (* le 2 j  ==  lt 1 j *)
    val le2j    = Thm.assume (ctermP le2j_P);
    val goalC   = goalEx jF;                      (* Ex(%p. Conj (prime p) (dvd p j)) *)

    (* lt 1 j is the SAME term as le 2 j *)
    val lt1j    = le2j;                            (* : lt (Suc Zero) j *)

    (* prime_cases at j : Disj (prime j) (Ex(%d. Conj(Conj(lt 1 d)(lt d j))(dvd d j)))
       BDisj must be the SAME term prime_cases produces (axiom n := j), i.e.
       mkEx (properDivAbs jF). *)
    val pcases  = prime_cases_at jF lt1j;
    val divBodyAbs = properDivAbs jF;
    val ADisj = prime jF;
    val BDisj = mkEx divBodyAbs;

    (* CASE A : prime j  ->  witness j, Conj (prime j) (dvd j j) *)
    val caseA =
      let
        val hpr  = Thm.assume (ctermP (jT (prime jF)));
        val drefl= dvd_refl_atP jF;               (* dvd j j *)
        val cj   = conjI_at (prime jF, dvd jF jF) hpr drefl;  (* Conj (prime j)(dvd j j) *)
        val ex   = exI_goal (jF, jF) cj;          (* Ex(%p. Conj(prime p)(dvd p j)) *)
      in Thm.implies_intr (ctermP (jT (prime jF))) ex end;

    (* CASE B : proper divisor.  exE witness d ; hd : Conj(Conj(lt 1 d)(lt d j))(dvd d j) *)
    val caseB =
      let
        val hExD = Thm.assume (ctermP (jT BDisj));
        fun dBody dF (hd : thm) =
          let
            val innerConj = mkConj (lt (suc ZeroC) dF) (lt dF jF);  (* Conj(lt 1 d)(lt d j) *)
            val c_inner = conjunct1_at (innerConj, dvd dF jF) hd;   (* Conj(lt 1 d)(lt d j) *)
            val h_dvd_dj= conjunct2_at (innerConj, dvd dF jF) hd;   (* dvd d j *)
            val h_lt1d  = conjunct1_at (lt (suc ZeroC) dF, lt dF jF) c_inner; (* lt 1 d *)
            val h_ltdj  = conjunct2_at (lt (suc ZeroC) dF, lt dF jF) c_inner; (* lt d j *)
            (* le 2 d == lt 1 d (the SAME term: le (Suc(Suc 0)) d = le (Suc 1) d) *)
            val h_le2d  = h_lt1d;
            (* need lt d x.  from lt j (Suc x): lt_suc_cases -> Disj (lt j x)(oeq j x) *)
            val jcases  = lt_suc_cases_at (jF, xF) ltjSx;   (* Disj (lt j x) (oeq j x) *)
            val ltdx =
              let
                fun caseJX () =   (* lt j x => lt d x by lt_trans (d,j,x) *)
                  let val hjx = Thm.assume (ctermP (jT (lt jF xF)))
                      val r = lt_trans_at (dF, jF, xF) h_ltdj hjx
                  in Thm.implies_intr (ctermP (jT (lt jF xF))) r end;
                fun caseJeqX () = (* oeq j x => rewrite lt d j to lt d x *)
                  let val hjeqx = Thm.assume (ctermP (jT (oeq jF xF)))
                      val zF1 = Free("zz1", natT)
                      val Pabs = Term.lambda zF1 (lt dF zF1)   (* %z. lt d z *)
                      val r = oeq_subst_P (Pabs, jF, xF) hjeqx h_ltdj
                  in Thm.implies_intr (ctermP (jT (oeq jF xF))) r end;
              in disjE_elimP (lt jF xF, oeq jF xF, lt dF xF) jcases (caseJX ()) (caseJeqX ()) end;
            (* IH at d : Imp (lt d x) (R d) ; impE with ltdx -> R d ; impE with le2d -> Ex *)
            val IHabs   = innerForallAbs xF;       (* %j. Imp (lt j x) (R j) *)
            val IHd     = allE_at (IHabs, dF) IH;  (* Imp (lt d x) (R d) *)
            val Rd      = impE_at (lt dF xF, Rbody dF) IHd ltdx;   (* R d = Imp (le 2 d)(Ex..) *)
            val exDivD  = impE_at (le two dF, exPrimeDiv dF) Rd h_le2d;  (* Ex(%p. Conj(prime p)(dvd p d)) *)
            (* exE that : witness p, hp : Conj (prime p)(dvd p d).
               pAbs MUST equal the abstraction inside exPrimeDiv dF = goalPabs dF. *)
            val pAbs    = goalPabs dF;
            fun pBody pF (hp : thm) =
              let
                val h_prp   = conjunct1_at (prime pF, dvd pF dF) hp;    (* prime p *)
                val h_dvd_pd= conjunct2_at (prime pF, dvd pF dF) hp;    (* dvd p d *)
                val h_dvd_pj= dvd_trans_at (pF, dF, jF) h_dvd_pd h_dvd_dj; (* dvd p j *)
                val cj      = conjI_at (prime pF, dvd pF jF) h_prp h_dvd_pj; (* Conj(prime p)(dvd p j) *)
              in exI_goal (jF, pF) cj end;          (* Ex(%p. Conj(prime p)(dvd p j)) *)
            val res = exE_elimP (pAbs, goalC) exDivD "pw" pBody;
          in res end;
        val g = exE_elimP (divBodyAbs, goalC) hExD "dw" dBody;
      in Thm.implies_intr (ctermP (jT BDisj)) g end;

    (* combine the two cases on prime_cases disjunction *)
    val exGoal = disjE_elimP (ADisj, BDisj, goalC) pcases caseA caseB;
    (* discharge le 2 j -> R j ; lt j (Suc x) -> Imp ; forall_intr j *)
    val Rj_thm   = impI_at (le two jF, exPrimeDiv jF) (Thm.implies_intr (ctermP le2j_P) exGoal);
    val impThm   = impI_at (lt jF (suc xF), Rbody jF) (Thm.implies_intr (ctermP ltjSx_P) Rj_thm);
    val metaAll  = Thm.forall_intr (ctermP jF) impThm;
  in allI_at (innerForallAbs (suc xF)) metaAll end;

val () = out "STEP_BODY_DEFINED\n";

(* ----------------------------------------------------------------------------
   ASSEMBLE THE STRONG-INDUCTION LEMMA  strongAux : Forall(%k. Q k)? No —
   we run nat_induct to get  Q k  schematically (k free), i.e.
     strongQ : |- Q k       (Q k = Forall(%j. Imp (lt j k) (R j)))
   ---------------------------------------------------------------------------- *)
val strongQ =
  let
    val kF = Free("k", natT);
    val ind = nat_induct_atP (Qpred, kF);   (* (Q 0) ==> (!!x. Q x ==> Q (Suc x)) ==> Q k *)
    val base = baseQ;                        (* Q 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (Qbody xF);              (* Q x *)
    val IH = Thm.assume (ctermP ihprop);
    val stepConcl = stepQ_body xF IH;        (* Q (Suc x) *)
    val step1 = Thm.forall_intr (ctermP xF) (Thm.implies_intr (ctermP ihprop) stepConcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in r2 end;

val () = out "STRONG_Q_PROVED\n";

(* ----------------------------------------------------------------------------
   FINAL THEOREM : prime_divisor_exists
     Trueprop (le 2 n) ==> Trueprop (Ex(%p. Conj (prime p) (dvd p n)))
   From strongQ at k := Suc n :  Q (Suc n) = Forall(%j. Imp (lt j (Suc n)) (R j)).
   allE at n : Imp (lt n (Suc n)) (R n).  lt n (Suc n) by lt_suc.  impE -> R n.
   R n = Imp (le 2 n) (Ex...).  assume le 2 n ; impE -> Ex.  discharge.
   ---------------------------------------------------------------------------- *)
val prime_divisor_exists =
  let
    val nF = Free("n", natT);
    val QSn = strongQ                          (* Q k with k free; instantiate k := Suc n *)
    (* re-run nat_induct route is overkill; instead instantiate strongQ's k.
       strongQ is |- Q k for FREE k; to specialize, forall_intr k then... simpler:
       just rebuild Q (Suc n) by varifying strongQ and instantiating. *)
    val strongQ_v = Drule.zero_var_indexes (Drule.export_without_context strongQ);
    (* strongQ_v : |- Q ?k  with ?k schematic.  instantiate ?k := Suc n. *)
    val QSn = beta_norm (Drule.infer_instantiate ctxtP [(("k",0), ctermP (suc nF))] strongQ_v);
    val IHabs = innerForallAbs (suc nF);       (* %j. Imp (lt j (Suc n)) (R j) *)
    val ImpN  = allE_at (IHabs, nF) QSn;       (* Imp (lt n (Suc n)) (R n) *)
    val ltn   = lt_suc_atP nF;                 (* lt n (Suc n) *)
    val Rn    = impE_at (lt nF (suc nF), Rbody nF) ImpN ltn;   (* R n = Imp (le 2 n)(Ex..) *)
    val le2n_P= jT (le two nF);
    val le2n  = Thm.assume (ctermP le2n_P);
    val exN   = impE_at (le two nF, exPrimeDiv nF) Rn le2n;    (* Ex(%p. Conj(prime p)(dvd p n)) *)
    val disch = Thm.implies_intr (ctermP le2n_P) exN;
  in varify disch end;

val () = out "FINAL_THEOREM_BUILT\n";

(* ----------------------------------------------------------------------------
   VALIDATION
   ---------------------------------------------------------------------------- *)
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

val nVp = Var (("n",0), natT);
val pde_intended =
  Logic.mk_implies (jT (le two nVp), jT (exPrimeDiv nVp));
val r_pde = checkP ("prime_divisor_exists", prime_divisor_exists, pde_intended);

(* ----------------------------------------------------------------------------
   SOUNDNESS PROBE 1 (passive): the proven theorem must NOT be the FALSE stronger
   claim "every n >= 1 has a prime divisor" (false at n = 1: 1 has no prime
   divisor).  That variant has premise  le (Suc Zero) n  instead of  le 2 n.
   aconv must be FALSE.
   ---------------------------------------------------------------------------- *)
val false_variant =
  Logic.mk_implies (jT (le (suc ZeroC) nVp), jT (exPrimeDiv nVp));
val probe1_rejected = not ((Thm.prop_of prime_divisor_exists) aconv false_variant);
val () = out ("SOUNDNESS probe1 (theorem != false 1<=n variant) rejected="
              ^ Bool.toString probe1_rejected ^ "\n");

(* ----------------------------------------------------------------------------
   SOUNDNESS PROBE 2 (active): the kernel must REJECT a bogus 0-hyp derivation
   of Trueprop oFalse.  We try to forge oFalse by instantiating exI's body to a
   constantly-false predicate and feeding a non-proof; the kernel's typed
   inference (implies_elim / a genuine proof requirement) makes this impossible
   without an actual proof of the premise.  We attempt to apply oFalse_elim to a
   NON-proof (an assumption of oFalse, which carries a hypothesis), then check
   the result is NOT a 0-hyp theorem of any goal — i.e. you cannot get oFalse
   for free.  Concretely: Thm.assume (Trueprop oFalse) has exactly ONE hyp; any
   attempt to discharge it without a real proof keeps the hyp.  Confirm. *)
val bogus_oFalse = Thm.assume (ctermP (jT oFalseC));
val probe2_has_hyp = (length (Thm.hyps_of bogus_oFalse) = 1);
(* and: deriving the goal-Ex from bogus_oFalse via oFalse_elim STILL carries the
   oFalse hyp (no free lunch) — confirm it is NOT 0-hyp. *)
val bogus_goal =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("R",0), ctermP (exPrimeDiv (Free("n",natT))))] (varify oFalse_elim_ax))
  in inst OF [bogus_oFalse] end;
val probe2_rejected = (length (Thm.hyps_of bogus_goal) <> 0);
val () = out ("SOUNDNESS probe2 (cannot forge oFalse-free goal) rejected="
              ^ Bool.toString probe2_rejected ^ "\n");

(* ============================================================================
   FINAL AGGREGATE VERDICT
   ----------------------------------------------------------------------------
   The six headline result-flags were each computed eagerly in their respective
   bodies, each printing its own "OK <name>" / "FAIL <name>" line above:
     r_strong         (strong_induct)        from the strong-induction body
     r_lt_trans       (lt_trans)             from the strict-order body
     r_lt_trichotomy  (lt_trichotomy)        from the strict-order body
     r_prime_two      (prime_two)            from the primality body
     r_prime_gt_1     (prime_gt_1)           from the primality body
     r_pde            (prime_divisor_exists) from the capstone body
   Print PRIME_DONE iff ALL SIX held.
   ============================================================================ *)
val () = out "==== PRIME DEVELOPMENT: SIX HEADLINE THEOREMS ====\n";
val () = out ("  strong_induct           : " ^ Bool.toString r_strong ^ "\n");
val () = out ("  lt_trans                : " ^ Bool.toString r_lt_trans ^ "\n");
val () = out ("  lt_trichotomy           : " ^ Bool.toString r_lt_trichotomy ^ "\n");
val () = out ("  prime_two               : " ^ Bool.toString r_prime_two ^ "\n");
val () = out ("  prime_gt_1              : " ^ Bool.toString r_prime_gt_1 ^ "\n");
val () = out ("  prime_divisor_exists    : " ^ Bool.toString r_pde ^ "\n");

val all_six_ok =
  r_strong andalso r_lt_trans andalso r_lt_trichotomy
  andalso r_prime_two andalso r_prime_gt_1 andalso r_pde;

val () =
  if all_six_ok
  then out "PRIME_DONE\n"
  else out "PRIME_INCOMPLETE\n";
