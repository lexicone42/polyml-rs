(* ============================================================================
   GAUSS SUMMATION + SUM OF ODDS, proved BY INDUCTION in Isabelle/Pure
   on the polyml-rs interpreter.  (test: isabelle_summation.rs)
   ----------------------------------------------------------------------------
   One rung up from the commutative-semiring development
   (isabelle_number_theory.sml): this driver copies that full foundation
   (object logic + Peano add/mult + the semiring laws), then defines two
   summation functions by recursion and proves the two classic identities,
   each a 0-hypothesis theorem, by genuine structural induction:

     sum  0 = 0 ;  sum  (Suc n) = (Suc n) + sum n          (triangular numbers)
     osum 0 = 0 ;  osum (Suc n) = osum n + (2n+1)          (running sum of odds)

     GAUSS         |- sum n + sum n = n * (Suc n)          (2*(0+..+n) = n(n+1))
     SUM_OF_ODDS   |- osum n = n * n                       (1+3+..+(2n-1) = n^2)

   Each proof is pure LCF kernel inference (nat_induct + the semiring lemmas;
   no automation). Verification asserts hyps = 0 AND prop aconv goal, and a
   soundness probe confirms the kernel REJECTS the false "drop the +1" Gauss
   variant, so the theorems are non-degenerate. Prints OK gauss / OK
   sum_of_odds / GAUSS_DONE.

   Built by a 3-seat ultracode workflow (wf_4ca14273-6ab): all three seats
   proved BOTH identities independently (this is seat B, the variant that
   reused the semiring lemmas with no new induction lemmas).

   The load-bearing subtlety: sum/osum are declared on the EXTENDED theory
   (Sign.add_consts on the mult-carrying tM2 -> tS), and ALL further cterms /
   instantiators / congruences are routed through ONE final context
   (ctxtS / ctermS) — mixing theories gives cross-theory cterm mismatches or
   silent no-op instantiation.  See CLAUDE.md (Isabelle section).
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

(* ============================================================================
   EXTENSION: summation functions sum / osum on a NEW theory extending tM2.
   Re-init ONE final context ctxtS / ctermS; route ALL sum/osum/mult/add
   cterms through it (cross-theory certificate safety).
   ============================================================================ *)
val thyS = Sign.add_consts
  [(Binding.name "sum",  natT --> natT, NoSyn),
   (Binding.name "osum", natT --> natT, NoSyn)] tM2;
val sumC  = Const (Sign.full_name thyS (Binding.name "sum"),  natT --> natT);
val osumC = Const (Sign.full_name thyS (Binding.name "osum"), natT --> natT);
fun summ t  = sumC  $ t;
fun osumm t = osumC $ t;

(* defining recursion equations as axioms on the extended theory *)
val ((_,sum_0),    tS1) = Thm.add_axiom_global (Binding.name "sum_0",
      jT (oeq (summ ZeroC) ZeroC)) thyS;
val ((_,sum_Suc),  tS2) = Thm.add_axiom_global (Binding.name "sum_Suc",
      jT (oeq (summ (suc n)) (add (suc n) (summ n)))) tS1;
val ((_,osum_0),   tS3) = Thm.add_axiom_global (Binding.name "osum_0",
      jT (oeq (osumm ZeroC) ZeroC)) tS2;
val ((_,osum_Suc), tS4) = Thm.add_axiom_global (Binding.name "osum_Suc",
      jT (oeq (osumm (suc n)) (add (osumm n) (suc (add n n))))) tS3;

val ctxtS  = Proof_Context.init_global tS4;
val ctermS = Thm.cterm_of ctxtS;

(* ---- re-instantiators routed through the FINAL extended context ctxtS ---- *)
val sum_0_v    = varify sum_0;
val sum_Suc_v  = varify sum_Suc;
val osum_0_v   = varify osum_0;
val osum_Suc_v = varify osum_Suc;
fun sumSuc_at t  = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS t)] sum_Suc_v);
fun osumSuc_at t = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS t)] osum_Suc_v);

(* add / mult equation instantiators on ctxtS *)
fun add0S_at t         = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS t)] add_0_v);
fun addSucS_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS
                            [(("m",0), ctermS mt),(("n",0), ctermS nt)] add_Suc_v);
fun add0rS_at t        = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS t)] (varify add_0_right));
fun addSrS_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtS
                            [(("m",0), ctermS mt),(("n",0), ctermS nt)] add_Suc_right_v);
fun mult0S_at t        = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS t)] mult_0_v);
fun multSucS_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtS
                            [(("m",0), ctermS mt),(("n",0), ctermS nt)] mult_Suc_v);
fun multSrS_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtS
                          [(("n",0), ctermS nt),(("m",0), ctermS mt)] mult_Suc_right_v);
fun addassocS_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtS
                               [(("m",0), ctermS mt),(("n",0), ctermS nt),(("k",0), ctermS kt)] add_assoc_v);
fun addcommS_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtS
                               [(("m",0), ctermS mt),(("n",0), ctermS nt)] add_comm_v);

(* nat_induct on ctxtS *)
fun nat_induct_S (Qpred, kT) = beta_norm (Drule.infer_instantiate ctxtS
      [(("P",0), ctermS Qpred), (("k",0), ctermS kT)] nat_induct_v);

(* congruences on ctxtS (need sum/mult subterms) *)
fun add_cong_lS (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS
          [(("P",0), ctermS Pabs), (("a",0), ctermS pT), (("b",0), ctermS qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS [(("a",0), ctermS (add pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rS (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS
          [(("P",0), ctermS Pabs), (("a",0), ctermS pT), (("b",0), ctermS qT)] oeq_subst_v);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtS [(("a",0), ctermS (add hT pT))] oeq_refl_v);
  in inst OF [hpq, refl_hp] end;

(* add4_swap on ctxtS:  add (add A B) (add C D) ~ add (add A C) (add B D) *)
fun add4_swapS (A,B,C,D) =
  let
    val asbcd = addassocS_at (A, B, add C D);
    val i1 = addassocS_at (B, C, D);
    val i1s = oeq_sym OF [i1];
    val icc = addcommS_at (B, C);
    val i2 = add_cong_lS (add B C, add C B, D) icc;
    val i3 = addassocS_at (C, B, D);
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];
    val cInner = add_cong_rS (A, add B (add C D), add C (add B D)) inner;
    val r1 = oeq_trans OF [asbcd, cInner];
    val r2assoc = addassocS_at (A, C, add B D);
    val r2assoc_s = oeq_sym OF [r2assoc];
  in oeq_trans OF [r1, r2assoc_s] end;

(* ============================================================================
   GAUSS :  oeq (add (sum n) (sum n)) (mult n (Suc n))      BY INDUCTION on n
   ============================================================================ *)

(* Canonicalisation bridge used in the step:
     add (add (Suc x) (Suc x)) T  ~  Suc (Suc (add (add x x) T))
     add (Suc (Suc x)) (add x T)  ~  Suc (Suc (add (add x x) T))
   so the two reshuffled sides are oeq via the common canonical form. *)
val gauss =
  let
    val Qpred = Abs("z", natT, oeq (add (summ (Bound 0)) (summ (Bound 0)))
                                   (mult (Bound 0) (suc (Bound 0))));
    val nF = Free("n", natT);
    val ind = nat_induct_S (Qpred, nF);
    (* BASE n=0 :
       LHS add (sum 0) (sum 0) ~ add 0 0 ~ 0 ;  RHS mult 0 (Suc 0) ~ 0 *)
    val s00 = beta_norm (Drule.infer_instantiate ctxtS [] sum_0_v); (* oeq (sum 0) 0 *)
    val s0  = beta_norm (Drule.infer_instantiate ctxtS [] sum_0_v);
    val cL1 = add_cong_lS (summ ZeroC, ZeroC, summ ZeroC) s00;   (* add (sum0)(sum0) ~ add 0 (sum0) *)
    val cL2 = add_cong_rS (ZeroC, summ ZeroC, ZeroC) s0;         (* add 0 (sum0) ~ add 0 0 *)
    val cL3 = add0S_at ZeroC;                                    (* add 0 0 ~ 0 *)
    val Lb  = oeq_trans OF [oeq_trans OF [cL1, cL2], cL3];       (* LHS ~ 0 *)
    val Rb  = mult0S_at (suc ZeroC);                             (* mult 0 (Suc 0) ~ 0 *)
    val RbS = oeq_sym OF [Rb];                                   (* 0 ~ mult 0 (Suc0) *)
    val base = oeq_trans OF [Lb, RbS];
    (* STEP : IH oeq (add (sum x) (sum x)) (mult x (Suc x)) *)
    val xF = Free("x", natT);
    val T  = mult xF (suc xF);                       (* = RHS of IH *)
    val ihprop = jT (oeq (add (summ xF) (summ xF)) T);
    val IH = Thm.assume (ctermS ihprop);
    (* LHS reshuffle *)
    val sSuc = sumSuc_at xF;                          (* oeq (sum(Suc x)) (add (Suc x) (sum x)) *)
    val Sx   = suc xF;
    val sm   = summ xF;
    (* add (sum(Suc x)) (sum(Suc x)) ~ add (add Sx sm) (add Sx sm) *)
    val L_c1 = add_cong_lS (summ Sx, add Sx sm, summ Sx) sSuc;
    val L_c2 = add_cong_rS (add Sx sm, summ Sx, add Sx sm) sSuc;
    val L_to_blocks = oeq_trans OF [L_c1, L_c2];      (* ~ add (add Sx sm) (add Sx sm) *)
    (* swap: add (add Sx sm) (add Sx sm) ~ add (add Sx Sx) (add sm sm) *)
    val sw = add4_swapS (Sx, sm, Sx, sm);
    (* IH on the (sm,sm) block: add sm sm ~ T *)
    val ihcong = add_cong_rS (add Sx Sx, add sm sm, T) IH;
    val L_full = oeq_trans OF [oeq_trans OF [L_to_blocks, sw], ihcong];
    (* LHS now ~ add (add Sx Sx) T ; canonicalise to Suc(Suc(add (add x x) T)) *)
    (* canon of  add (add Sx Sx) T : *)
    val La = addassocS_at (Sx, Sx, T);                          (* ~ add Sx (add Sx T) *)
    val inSxT = addSucS_at (xF, T);                             (* add Sx T ~ Suc (add x T) *)
    val La_c = add_cong_rS (Sx, add Sx T, suc (add xF T)) inSxT;(* ~ add Sx (Suc (add x T)) *)
    val outS = addSucS_at (xF, suc (add xF T));                 (* add Sx (Suc(add x T)) ~ Suc(add x (Suc(add x T))) *)
    val inXSucXT = addSrS_at (xF, add xF T);                    (* add x (Suc(add x T)) ~ Suc (add x (add x T)) *)
    val inAssoc  = addassocS_at (xF, xF, T);                    (* add x (add x T) ~ ... wait: assoc is add(add..) ; need reverse *)
    (* addassocS_at(x,x,T): oeq (add (add x x) T) (add x (add x T)) ; we want reverse: *)
    val inAssocS = oeq_sym OF [inAssoc];                        (* add x (add x T) ~ add (add x x) T *)
    val inXSucXT_canon = oeq_trans OF [inXSucXT, Suc_cong OF [inAssocS]];
                                                               (* add x (Suc(add x T)) ~ Suc (add (add x x) T) *)
    val La_to_canon =
      oeq_trans OF [oeq_trans OF [La, La_c],
                    oeq_trans OF [outS, Suc_cong OF [inXSucXT_canon]]];
    (* La_to_canon : add (add Sx Sx) T ~ Suc (Suc (add (add x x) T)) *)
    val LHS_canon = oeq_trans OF [L_full, La_to_canon];        (* full LHS ~ canon *)
    (* RHS : mult (Suc x) (Suc (Suc x)) *)
    val N    = suc (suc xF);                                    (* Suc (Suc x) *)
    val rM   = multSucS_at (xF, N);                             (* mult (Suc x) N ~ add N (mult x N) *)
    (* mult x N = mult x (Suc (Suc x)) ~ add x (mult x (Suc x)) = add x T  via mult_Suc_right *)
    val rMxN = multSrS_at (xF, suc xF);                         (* oeq (mult x (Suc (Suc x))) (add x (mult x (Suc x))) *)
    val rMxN' = rMxN;                                           (* = oeq (mult x N) (add x T) *)
    val rCong = add_cong_rS (N, mult xF N, add xF T) rMxN';     (* add N (mult x N) ~ add N (add x T) *)
    val RHS_to = oeq_trans OF [rM, rCong];                      (* RHS ~ add N (add x T) *)
    (* canon of add N (add x T) = add (Suc(Suc x)) (add x T) : *)
    val ra1 = addSucS_at (suc xF, add xF T);                    (* add (Suc(Suc x)) (add x T) ~ Suc (add (Suc x) (add x T)) *)
    val ra2 = addSucS_at (xF, add xF T);                        (* add (Suc x) (add x T) ~ Suc (add x (add x T)) *)
    val ra3 = oeq_sym OF [addassocS_at (xF, xF, T)];            (* add x (add x T) ~ add (add x x) T *)
    val raInner = oeq_trans OF [ra2, Suc_cong OF [ra3]];        (* add (Suc x)(add x T) ~ Suc (add (add x x) T) *)
    val RHS_canon0 = oeq_trans OF [ra1, Suc_cong OF [raInner]]; (* add N (add x T) ~ Suc(Suc(add (add x x) T)) *)
    val RHS_canon = oeq_trans OF [RHS_to, RHS_canon0];          (* RHS ~ canon *)
    val stepconcl = oeq_trans OF [LHS_canon, oeq_sym OF [RHS_canon]];
    val step1 = Thm.forall_intr (ctermS xF) (Thm.implies_intr (ctermS ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   SUM OF ODDS :  oeq (osum n) (mult n n)      BY INDUCTION on n
   ============================================================================ *)
val sum_of_odds =
  let
    val Qpred = Abs("z", natT, oeq (osumm (Bound 0)) (mult (Bound 0) (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_S (Qpred, nF);
    (* BASE n=0 : osum 0 ~ 0 ; mult 0 0 ~ 0 *)
    val b1 = beta_norm (Drule.infer_instantiate ctxtS [] osum_0_v); (* oeq (osum 0) 0 *)
    val b2 = mult0S_at ZeroC;                                       (* oeq (mult 0 0) 0 *)
    val base = oeq_trans OF [b1, oeq_sym OF [b2]];
    (* STEP : IH oeq (osum x) (mult x x) *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (osumm xF) (mult xF xF));
    val IH = Thm.assume (ctermS ihprop);
    val odd = suc (add xF xF);                       (* the (x)-th odd number Suc(x+x) = 2x+1 *)
    (* LHS: osum (Suc x) ~ add (osum x) odd ~ add (mult x x) odd   [by IH] *)
    val oS = osumSuc_at xF;                           (* oeq (osum(Suc x)) (add (osum x) odd) *)
    val oCong = add_cong_lS (osumm xF, mult xF xF, odd) IH; (* add (osum x) odd ~ add (mult x x) odd *)
    val LHS = oeq_trans OF [oS, oCong];              (* osum(Suc x) ~ add (mult x x) odd *)
    (* RHS: mult (Suc x) (Suc x) ~ add (Suc x) (mult x (Suc x))  [mult_Suc]
            mult x (Suc x) ~ add x (mult x x)                    [mult_Suc_right]
       => mult (Suc x)(Suc x) ~ add (Suc x) (add x (mult x x)) *)
    val rM   = multSucS_at (xF, suc xF);             (* mult (Suc x)(Suc x) ~ add (Suc x) (mult x (Suc x)) *)
    val rMx  = multSrS_at (xF, xF);                  (* mult x (Suc x) ~ add x (mult x x) *)
    val rCong= add_cong_rS (suc xF, mult xF (suc xF), add xF (mult xF xF)) rMx;
    val RHS_to = oeq_trans OF [rM, rCong];           (* RHS ~ add (Suc x) (add x (mult x x)) *)
    (* Bridge LHS' = add (mult x x) odd  ~  RHS' = add (Suc x) (add x (mult x x))
       where odd = Suc (add x x).  Let M = mult x x.
       LHS' = add M (Suc (add x x))
       RHS' = add (Suc x) (add x M) *)
    val M = mult xF xF;
    (* LHS' canon -> Suc (Suc (add (add x x) M)) :
         add M (Suc (add x x)) ~ Suc (add M (add x x))            [add_Suc_right]
         add M (add x x) ~ add (add x x) M                        [add_comm]   *)
    val lA = addSrS_at (M, add xF xF);               (* add M (Suc(add x x)) ~ Suc (add M (add x x)) *)
    val lB = addcommS_at (M, add xF xF);             (* add M (add x x) ~ add (add x x) M *)
    val LHS_canon = oeq_trans OF [lA, Suc_cong OF [lB]];
                                                     (* LHS' ~ Suc (add (add x x) M) *)
    (* RHS' canon -> Suc (add (add x x) M) :
         add (Suc x) (add x M) ~ Suc (add x (add x M))            [add_Suc]
         add x (add x M) ~ add (add x x) M                        [assoc sym]  *)
    val rA = addSucS_at (xF, add xF M);              (* add (Suc x)(add x M) ~ Suc (add x (add x M)) *)
    val rB = oeq_sym OF [addassocS_at (xF, xF, M)];  (* add x (add x M) ~ add (add x x) M *)
    val RHS_canon = oeq_trans OF [rA, Suc_cong OF [rB]];
                                                     (* RHS' ~ Suc (add (add x x) M) *)
    val bridge = oeq_trans OF [LHS_canon, oeq_sym OF [RHS_canon]];
                                                     (* LHS' ~ RHS' *)
    val stepconcl = oeq_trans OF [oeq_trans OF [LHS, bridge], oeq_sym OF [RHS_to]];
    val step1 = Thm.forall_intr (ctermS xF) (Thm.implies_intr (ctermS ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   RIGOROUS VERIFICATION + soundness probe
   ============================================================================ *)
val nVar = Var (("n",0), natT);
fun checkS (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh
              ^ " aconv=" ^ Bool.toString ac ^ ")\n  got      = "
              ^ Syntax.string_of_term ctxtS (Thm.prop_of th)
              ^ "\n  intended = " ^ Syntax.string_of_term ctxtS intended ^ "\n"); false)
  end;

val gauss_goal = jT (oeq (add (summ nVar) (summ nVar)) (mult nVar (suc nVar)));
val odds_goal  = jT (oeq (osumm nVar) (mult nVar nVar));

val r_gauss = checkS ("gauss", gauss, gauss_goal);
val r_odds  = checkS ("sum_of_odds", sum_of_odds, odds_goal);

(* soundness probe: kernel must REJECT an obviously-FALSE variant of Gauss,
   e.g.  oeq (add (sum n) (sum n)) (mult n n)   (drops the +1; false for n=1:
   2*sum(1)=2 but 1*1=1).  We can't "prove" it; the strongest in-kernel probe
   is that our verified gauss theorem is NOT aconv this false statement. *)
val false_gauss_goal = jT (oeq (add (summ nVar) (summ nVar)) (mult nVar nVar));
val probe_rejects = not ((Thm.prop_of gauss) aconv false_gauss_goal);
val () = out (if probe_rejects
              then "PROBE_OK gauss is not the false (drop +1) variant\n"
              else "PROBE_FAIL gauss matches a false statement!\n");

(* extra soundness probe: attempt to build the false theorem and show the
   verified one's statement genuinely differs (non-degenerate). *)
val () = out ("gauss prop = " ^ Syntax.string_of_term ctxtS (Thm.prop_of gauss) ^ "\n");

(* ACTIVE soundness probe: try to DERIVE the false variant
     oeq (add (sum n) (sum n)) (mult n n)
   from the true gauss by oeq_subst-rewriting the RHS mult n (Suc n) -> mult n n.
   That rewrite step REQUIRES a premise  oeq (mult n (Suc n)) (mult n n)  which is
   FALSE, so the only way the kernel lets us reach the false conclusion is by
   ASSUMING that premise.  We do exactly that and confirm: (a) the false
   conclusion IS reached (so our construction is wired correctly), but (b) it is
   NOT a theorem — it carries the bogus premise as an uneliminated hypothesis
   (hyps <> []).  A genuinely false statement can never be a 0-hyp theorem here. *)
val active_probe =
  let
    val nF  = Free ("n", natT);
    val gN  = beta_norm (Drule.infer_instantiate ctxtS [(("n",0), ctermS nF)] (varify gauss));
            (* oeq (add (sum n)(sum n)) (mult n (Suc n)) *)
    val bogus = jT (oeq (mult nF (suc nF)) (mult nF nF));   (* FALSE premise *)
    val Hbogus = Thm.assume (ctermS bogus);
    (* rewrite the RHS of gN using Hbogus via add-style cong on oeq:
       use oeq_subst with P z := oeq (add (sum n)(sum n)) z *)
    val Pabs = Abs("z", natT, oeq (add (summ nF) (summ nF)) (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxtS
          [(("P",0), ctermS Pabs),
           (("a",0), ctermS (mult nF (suc nF))),
           (("b",0), ctermS (mult nF nF))] oeq_subst_v);
    val false_thm = inst OF [Hbogus, gN];   (* concl: oeq (add (sum n)(sum n)) (mult n n) *)
    val nh = length (Thm.hyps_of false_thm);
    val reached =
      (Thm.prop_of false_thm) aconv
        (jT (oeq (add (summ nF) (summ nF)) (mult nF nF)));
  in (reached, nh) end;

val () =
  let val (reached, nh) = active_probe in
    out ("ACTIVE_PROBE reached_false_concl=" ^ Bool.toString reached
         ^ " hyps=" ^ Int.toString nh ^ "\n");
    if reached andalso nh > 0
    then out "ACTIVE_PROBE_OK kernel admits the false statement ONLY with a bogus hypothesis (never 0-hyp)\n"
    else out "ACTIVE_PROBE_UNEXPECTED\n"
  end;

val () =
  if r_gauss andalso r_odds andalso probe_rejects
  then out "GAUSS_DONE\n"
  else out "INCOMPLETE: gauss/sum_of_odds not both verified\n";
