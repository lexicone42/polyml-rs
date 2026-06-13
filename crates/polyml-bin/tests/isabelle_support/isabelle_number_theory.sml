(* ============================================================================
   THE NATURAL NUMBERS FORM A COMMUTATIVE SEMIRING — BY INDUCTION
   ----------------------------------------------------------------------------
   One self-contained Isabelle/Pure ML driver, run on the Rust reimplementation
   of PolyML (`poly run /tmp/isabelle_pure`).  It builds a tiny first-order
   object logic + Peano addition and multiplication ONCE, then derives, as
   genuine 0-hypothesis kernel theorems by structural induction:

       add_0_right    : oeq (add n 0) n
       add_comm       : oeq (add m n) (add n m)
       add_assoc      : oeq (add (add m n) k) (add m (add n k))
       mult_0_right   : oeq (mult n 0) 0
       mult_1_right   : oeq (mult n (Suc 0)) n
       mult_comm      : oeq (mult m n) (mult n m)
       mult_assoc     : oeq (mult (mult m n) k) (mult m (mult n k))
       left_distrib   : oeq (mult k (add m n)) (add (mult k m) (mult k n))
       right_distrib  : oeq (mult (add m n) k) (add (mult m k) (mult n k))

   Together that is exactly the axiom set of a COMMUTATIVE SEMIRING (N,+,*,0,1):
     - (N,+,0) commutative monoid          : add_0_right, add_comm, add_assoc
     - (N,*,1) commutative monoid          : mult_1_right, mult_comm, mult_assoc
     - 0 annihilates                        : mult_0_right
     - * distributes over +                 : left_distrib, right_distrib

   HOW THIS WAS BUILT
   ------------------
   Merged from four independently-verified single-law drivers
   (/tmp/isa_verify/law_0..3.sml) plus the add-law reference
   (isabelle_arithmetic.sml).  They share a near-identical foundation prefix;
   here it appears EXACTLY ONCE, followed by each law's proof body in
   dependency order:
       foundation
         -> add_0_right, add_Suc_right, add_comm, add_assoc
         -> mult_0_right, mult_Suc_right
         -> mult_comm
         -> right_distrib
         -> mult_assoc
         -> mult_1_right
         -> left_distrib   (direct induction, via a pure-add 4-way swap lemma)

   KEY SUBTLETIES (preserved from the source drivers):
     * Multiplication is declared on an EXTENDED theory (tM2); EVERY cterm,
       instantiator and congruence used in a mult goal is routed through the
       SAME final context (ctxtM/ctermM) to avoid cross-theory certificate
       mismatch or silent no-op instantiation.
     * Thm.add_axiom_global returns UNVARIFIED Free-form theorems — `varify`
       them (export_without_context + zero_var_indexes) before
       infer_instantiate / OF.
     * infer_instantiate and forall_elim do NOT beta-reduce — `beta_norm`
       after each instantiation.
     * Each shared lemma (mult_Suc_right, right_distrib, the congruences,
       add4_swap, ...) is proved / defined ONCE and reused.

   VERIFICATION: for each of the nine laws we assert
       length (Thm.hyps_of th) = 0      (a real theorem, no leftover hyps)
   AND Thm.prop_of th `aconv` <intended schematic goal>,
   printing "OK <name>" only when BOTH hold (else "FAIL <name>" with detail).
   The driver ends with "SEMIRING_OK" iff all nine fired.
   ============================================================================ *)

(* ---- MUST be first: generic context is thread-local, lost on reload ---- *)
val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

(* ============================================================================
   FOUNDATION : object logic (types o, nat) + Trueprop + Peano add + equality
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

(* equality: refl + subst (subst gives sym / trans / congruence) *)
val ((_,oeq_refl),  t3) = Thm.add_axiom_global (Binding.name "oeq_refl",  jT (oeq a a)) thy2;
val ((_,oeq_subst), t4) = Thm.add_axiom_global (Binding.name "oeq_subst",
      Logic.mk_implies (jT (oeq a b), Logic.mk_implies (jT (P $ a), jT (P $ b)))) t3;
(* add recursion equations (recursion on the 1st arg) *)
val ((_,add_0),   t5) = Thm.add_axiom_global (Binding.name "add_0",   jT (oeq (add ZeroC n) n)) t4;
val ((_,add_Suc), t6) = Thm.add_axiom_global (Binding.name "add_Suc",
      jT (oeq (add (suc m) n) (suc (add m n)))) t5;
(* INDUCTION:  P 0 ==> (!!x. P x ==> P (Suc x)) ==> P k *)
val k = Free ("k", natT); val x = Free ("x", natT);
val induct_prop = Logic.mk_implies (jT (P $ ZeroC),
      Logic.mk_implies (Logic.all x (Logic.mk_implies (jT (P $ x), jT (P $ (suc x)))), jT (P $ k)));
val ((_,nat_induct), thy) = Thm.add_axiom_global (Binding.name "nat_induct", induct_prop) t6;

val ctxt = Proof_Context.init_global thy;
val cterm = Thm.cterm_of ctxt;

(* helpers: varify a Free-carrying axiom to schematic; beta-normalise after elim *)
fun varify th = Drule.zero_var_indexes (Drule.export_without_context th);
fun beta_norm th = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;

val oeq_refl_v   = varify oeq_refl;
val oeq_subst_v  = varify oeq_subst;
val add_0_v      = varify add_0;
val add_Suc_v    = varify add_Suc;
val nat_induct_v = varify nat_induct;

(* ---- oeq_sym : oeq a b ==> oeq b a ---- *)
val oeq_sym =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm aF)] oeq_refl_v);
    val step = inst OF [Thm.assume (cterm (jT (oeq aF bF))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;

(* ---- oeq_trans : oeq a b ==> oeq b c ==> oeq a c ---- *)
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

(* ---- Suc_cong : oeq a b ==> oeq (Suc a) (Suc b) ---- *)
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

(* convenience: instantiate the add equations at ground terms (base ctxt) *)
fun add0_at t         = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_v);
fun addSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxt
                          [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_v);

(* add-congruence on LEFT / RIGHT operand (base ctxt) *)
fun add_cong_l_at (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm pT), (("b",0), cterm qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;

(* ============================================================================
   ADDITIVE COMMUTATIVE MONOID : add_0_right, add_Suc_right, add_comm, add_assoc
   ============================================================================ *)

(* ---- add_0_right : oeq (add n Zero) n   BY INDUCTION on n ---- *)
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

(* ---- add_Suc_right : oeq (add m (Suc n)) (Suc (add m n))   BY INDUCTION on m ---- *)
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

(* ---- add_comm : oeq (add m n) (add n m)   BY INDUCTION on m ---- *)
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

(* ---- add_assoc : oeq (add (add m n) k) (add m (add n k))   BY INDUCTION on m ---- *)
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
   MULTIPLICATION : declare const on the EXTENDED theory tM2, build the SINGLE
   final context ctxtM / ctermM through which ALL further cterms are routed.
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

(* instantiators on the FINAL extended context *)
fun mult0_at t         = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] mult_0_v);
fun multSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtM
                            [(("m",0), ctermM mt),(("n",0), ctermM nt)] mult_Suc_v);
fun add0M_at t         = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] add_0_v);
fun addSucM_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtM
                            [(("m",0), ctermM mt),(("n",0), ctermM nt)] add_Suc_v);

(* schematic / ground forms of the add laws on the extended context *)
val add_comm_v  = varify add_comm;
val add_assoc_v = varify add_assoc;
fun addcomm_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtM
                               [(("m",0), ctermM mt),(("n",0), ctermM nt)] add_comm_v);
fun addassoc_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtM
                               [(("m",0), ctermM mt),(("n",0), ctermM nt),(("k",0), ctermM kt)] add_assoc_v);

(* congruences on the FINAL extended context (need mult subterms) *)
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

(* ---- mult_0_right : oeq (mult n Zero) Zero   BY INDUCTION on n ---- *)
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

(* ---- mult_Suc_right : oeq (mult n (Suc m)) (add n (mult n m))   BY INDUCTION on n ---- *)
val mult_Suc_right =
  let
    val mFix = Free("m", natT);   (* the fixed parameter *)
    val Qpred = Abs("z", natT, oeq (mult (Bound 0) (suc mFix)) (add (Bound 0) (mult (Bound 0) mFix)));
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM nF)] nat_induct_v);
    (* BASE n=0 : both sides reduce to 0 *)
    val b1 = mult0_at (suc mFix);
    val r0 = mult0_at mFix;
    val rA = add0M_at (mult ZeroC mFix);
    val rChain = oeq_trans OF [rA, r0];
    val rChainSym = oeq_sym OF [rChain];
    val base = oeq_trans OF [b1, rChainSym];
    (* STEP : IH oeq (mult x (Suc m)) (add x (mult x m)) *)
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
    (* Bridge: add m (add x t) ~ add x (add m t), t = mult x m  (assoc + comm) *)
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

(* schematic + ground forms of mult_0_right / mult_Suc_right *)
val mult_0_right_v   = varify mult_0_right;
val mult_Suc_right_v = varify mult_Suc_right;
fun mult0r_at t       = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] mult_0_right_v);
fun multSr_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtM
                          [(("n",0), ctermM nt),(("m",0), ctermM mt)] mult_Suc_right_v);

(* ============================================================================
   MULTIPLICATIVE COMMUTATIVE MONOID & DISTRIBUTIVITY
   ============================================================================ *)

(* ---- mult_comm : oeq (mult m n) (mult n m)   BY INDUCTION on m ---- *)
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

(* ---- right_distrib : oeq (mult (add m n) k) (add (mult m k) (mult n k))
        BY INDUCTION on m  (n, k held fixed) ---- *)
val right_distrib =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (mult (add (Bound 0) nF) kF) (add (mult (Bound 0) kF) (mult nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM mF)] nat_induct_v);
    (* BASE m=0 *)
    val a0n = add0M_at nF;
    val Lb  = mult_cong_lM (add ZeroC nF, nF, kF) a0n;
    val m0k = mult0_at kF;
    val Rb1 = add_cong_lM (mult ZeroC kF, ZeroC, mult nF kF) m0k;
    val Rb2 = add0M_at (mult nF kF);
    val RbChain = oeq_trans OF [Rb1, Rb2];
    val RbSym = oeq_sym OF [RbChain];
    val base = oeq_trans OF [Lb, RbSym];
    (* STEP *)
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

(* schematic form of right_distrib, ground instantiator (used by mult_assoc) *)
val right_distrib_v = varify right_distrib;
fun rdist_at (aT,bT,kT) = beta_norm (Drule.infer_instantiate ctxtM
        [(("m",0), ctermM aT),(("n",0), ctermM bT),(("k",0), ctermM kT)] right_distrib_v);

(* ---- mult_assoc : oeq (mult (mult m n) k) (mult m (mult n k))
        BY INDUCTION on m  (n, k held fixed) ---- *)
val mult_assoc =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (mult (mult (Bound 0) nF) kF) (mult (Bound 0) (mult nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM mF)] nat_induct_v);
    (* BASE m=0 *)
    val m0n   = mult0_at nF;
    val L1    = mult_cong_lM (mult ZeroC nF, ZeroC, kF) m0n;
    val L2    = mult0_at kF;
    val Lbase = oeq_trans OF [L1, L2];
    val R0    = mult0_at (mult nF kF);
    val R0sym = oeq_sym OF [R0];
    val base  = oeq_trans OF [Lbase, R0sym];
    (* STEP *)
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

(* ---- mult_1_right : oeq (mult n (Suc Zero)) n
        Route: mult_Suc_right[n,0] -> cong-r(mult_0_right[n]) -> add_0_right[n] ---- *)
val add_0_right_vM = varify add_0_right;
fun add0rM_at t = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] add_0_right_vM);

val mult_1_right =
  let
    val nF = Free("n", natT);
    val s1 = multSr_at (nF, ZeroC);                         (* oeq (mult n (Suc 0)) (add n (mult n 0)) *)
    val m0 = mult0r_at nF;                                  (* oeq (mult n 0) 0 *)
    val cr = add_cong_rM (nF, mult nF ZeroC, ZeroC) m0;     (* oeq (add n (mult n 0)) (add n 0) *)
    val a0 = add0rM_at nF;                                  (* oeq (add n 0) n *)
    val c1 = oeq_trans OF [s1, cr];
    val c2 = oeq_trans OF [c1, a0];
  in varify c2 end;

(* ---- left_distrib : oeq (mult k (add m n)) (add (mult k m) (mult k n))
        BY INDUCTION on k  (m, n held fixed), via the pure-add 4-way swap:
          add (add A B) (add C D) = add (add A C) (add B D) ---- *)
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
   RIGOROUS VERIFICATION : each law is a 0-hyp theorem AND aconv its goal.
   ============================================================================ *)
val mV = Var (("m",0), natT);
val nV = Var (("n",0), natT);
val kV = Var (("k",0), natT);

(* check one law: assert 0 hyps AND prop aconv the intended schematic goal.
   Returns true iff both hold (printing OK / FAIL), so the SEMIRING_OK gate is a
   pure conjunction — no mutable state (the Isabelle ML namespace shadows `ref`). *)
fun check (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then
      (out ("OK " ^ nm ^ "\n"); true)
    else
      (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh
            ^ " aconv=" ^ Bool.toString ac
            ^ ")\n  got      = " ^ Syntax.string_of_term ctxtM (Thm.prop_of th)
            ^ "\n  intended = " ^ Syntax.string_of_term ctxtM intended ^ "\n");
       false)
  end;

val r_add_0   = check ("add_0_right",  add_0_right,  jT (oeq (add nV ZeroC) nV));
val r_add_c   = check ("add_comm",     add_comm,     jT (oeq (add mV nV) (add nV mV)));
val r_add_a   = check ("add_assoc",    add_assoc,    jT (oeq (add (add mV nV) kV) (add mV (add nV kV))));
val r_mul_0   = check ("mult_0_right", mult_0_right, jT (oeq (mult nV ZeroC) ZeroC));
val r_mul_1   = check ("mult_1_right", mult_1_right, jT (oeq (mult nV (suc ZeroC)) nV));
val r_mul_c   = check ("mult_comm",    mult_comm,    jT (oeq (mult mV nV) (mult nV mV)));
val r_mul_a   = check ("mult_assoc",   mult_assoc,   jT (oeq (mult (mult mV nV) kV) (mult mV (mult nV kV))));
val r_ldist   = check ("left_distrib", left_distrib, jT (oeq (mult kV (add mV nV)) (add (mult kV mV) (mult kV nV))));
val r_rdist   = check ("right_distrib",right_distrib,jT (oeq (mult (add mV nV) kV) (add (mult mV kV) (mult nV kV))));

val all_ok = r_add_0 andalso r_add_c andalso r_add_a
             andalso r_mul_0 andalso r_mul_1 andalso r_mul_c andalso r_mul_a
             andalso r_ldist andalso r_rdist;

val () =
  if all_ok
  then out "SEMIRING_OK\n"
  else out "INCOMPLETE: not all nine laws verified\n";
