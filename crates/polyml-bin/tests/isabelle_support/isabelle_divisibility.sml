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
