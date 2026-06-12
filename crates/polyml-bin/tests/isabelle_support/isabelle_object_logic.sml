(* isabelle_object_logic.sml — a minimal FIRST-ORDER OBJECT LOGIC built on
   Isabelle/Pure (programmatically, IFOL-style) with real theorems proved in it,
   all on the Rust PolyML interpreter via the warm /tmp/isabelle_pure checkpoint.

   The step from META-LOGIC to MATHEMATICS: Isabelle object logics ship as .thy
   files loaded through Thy_Info (needs PIDE, not loaded here), so we build the
   logic the way IFOL.thy does — a formula type `o`, judgment Trueprop :: o=>prop,
   connective/quantifier consts, and the natural-deduction rules as AXIOMS
   (Thm.add_axiom_global) — purely in ML, and prove with the kernel/tactics/
   resolution. Five connectives, each a checked object-level thm:
     conj   |- Trueprop (conj A B) ==> Trueprop (conj B A)          (commutativity)
     oimp   |- Trueprop (oimp A (oimp B A))                         (K / weakening)
     disj   |- Trueprop (disj A B) ==> Trueprop (disj B A)         (via disjE)
     All    |- Trueprop (All (%x. conj (P x) (Q x))) ==> Trueprop (All P)
     oeq    |- Trueprop (oeq a b) ==> Trueprop (oeq b a)           (symmetry via subst)
   Found by a 5-seat ultracode workflow (wf_570c4e06-017); all five verified.

   KEY LESSON: Thm.add_axiom_global returns the axiom UNVARIFIED (Free vars, not
   schematic) — to instantiate/resolve, varify first (Drule.generalize /
   Thm.generalize + zero_var_indexes, or Drule.export_without_context). forall_elim
   does not beta-reduce; beta-normalise before resolving.

   Run: poly run /tmp/isabelle_pure < this file *)

val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
val () = out "ISA_OBJLOGIC_START\n";

(* ===== conj ===== *)
local

val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global [(Binding.name "o", 0, NoSyn)] thy0;
val o_name = Sign.full_name thy1 (Binding.name "o");
val oT = Type (o_name, []);

val thy2 = Sign.add_consts
  [ (Binding.name "Trueprop", oT --> propT, NoSyn),
    (Binding.name "conj",     oT --> oT --> oT, NoSyn) ] thy1;
val Trueprop = Const (Sign.full_name thy2 (Binding.name "Trueprop"), oT --> propT);
val conj     = Const (Sign.full_name thy2 (Binding.name "conj"),     oT --> oT --> oT);
fun mkTP t      = Trueprop $ t;
fun mkConj a b  = conj $ a $ b;

val A = Free ("A", oT);
val B = Free ("B", oT);

val ((_, conjI),     thy3) = Thm.add_axiom_global
      (Binding.name "conjI",     Logic.list_implies ([mkTP A, mkTP B], mkTP (mkConj A B))) thy2;
val ((_, conjunct1), thy4) = Thm.add_axiom_global
      (Binding.name "conjunct1", Logic.mk_implies (mkTP (mkConj A B), mkTP A)) thy3;
val ((_, conjunct2), thy5) = Thm.add_axiom_global
      (Binding.name "conjunct2", Logic.mk_implies (mkTP (mkConj A B), mkTP B)) thy4;

val thy  = thy5;
val ctxt = Proof_Context.init_global thy;

val ct_hyp = Thm.cterm_of ctxt (mkTP (mkConj A B));
val hyp = Thm.assume ct_hyp;
val thA = Thm.implies_elim conjunct1 hyp;
val thB = Thm.implies_elim conjunct2 hyp;

val conjI_gen = Drule.generalize (Names.empty, Names.make_set ["A","B"]) conjI;
val gvars = Term.add_vars (Thm.prop_of conjI_gen) [];
val ixA = #1 (hd (filter (fn ((n,_),_) => n = "A") gvars));
val ixB = #1 (hd (filter (fn ((n,_),_) => n = "B") gvars));
val conjI_BA = Drule.infer_instantiate ctxt
      [(ixA, Thm.cterm_of ctxt B), (ixB, Thm.cterm_of ctxt A)] conjI_gen;
val bca = Thm.implies_elim (Thm.implies_elim conjI_BA thB) thA;
val comm = Thm.implies_intr ct_hyp bca;

val () = out ("=== THM comm_conj ===\n" ^ Thm.string_of_thm ctxt comm ^ "\n");
val expected = Logic.mk_implies (mkTP (mkConj A B), mkTP (mkConj B A));
val ok = Thm.prop_of comm aconv expected andalso null (Thm.hyps_of comm);
val () = out (if ok then "OK: verified  conj A B ==> conj B A  (0 hyps)\n" else "FAIL\n");
in val () = out ("RUNG conj " ^ (if ok then "OK" else "FAIL") ^ " :: " ^ Thm.string_of_thm ctxt comm ^ "\n") end;

(* ===== oimp ===== *)
local

val thy0 = Context.the_global_context ();

(* type o; build Type with FULL name (user-added types get the Pure. prefix) *)
val thy1 = Sign.add_types_global [(Binding.name "o", 0, NoSyn)] thy0;
val oN  = Sign.full_name thy1 (Binding.name "o");   (* Pure.o *)
val oT  = Type (oN, []);

(* Trueprop : o=>prop ; oimp : o=>o=>o  (NB: imp is reserved = Pure meta ==>) *)
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "oimp",     oT --> oT --> oT, NoSyn)] thy1;
val truepropN = Sign.full_name thy2 (Binding.name "Trueprop");
val oimpN     = Sign.full_name thy2 (Binding.name "oimp");

val TruepropC = Const (truepropN, oT --> propT);
val oimpC     = Const (oimpN, oT --> oT --> oT);
fun jT t       = TruepropC $ t;
fun mkimp a b  = oimpC $ a $ b;

val A = Free ("A", oT); val B = Free ("B", oT); val C = Free ("C", oT);

(* axioms: impI (A==>B)==>oimp A B ; mp oimp A B ==> A ==> B *)
val impI_prop = Logic.mk_implies (Logic.mk_implies (jT A, jT B), jT (mkimp A B));
val mp_prop   = Logic.mk_implies (jT (mkimp A B), Logic.mk_implies (jT A, jT B));
val ((_, impI), thy3) = Thm.add_axiom_global (Binding.name "impI", impI_prop) thy2;
val ((_, mp),   thy4) = Thm.add_axiom_global (Binding.name "mp",   mp_prop)   thy3;
val ctxt = Proof_Context.init_global thy4;

(* Frees -> schematic for resolution *)
val impI_r = Drule.export_without_context impI;
val mp_r   = Drule.export_without_context mp;

(* K via pure LCF kernel: meta-==> vs object-imp interplay *)
val impI_gen = impI |> Thm.forall_intr (Thm.cterm_of ctxt A)
                    |> Thm.forall_intr (Thm.cterm_of ctxt B);
fun impI_at a b = impI_gen |> Thm.forall_elim (Thm.cterm_of ctxt b)
                           |> Thm.forall_elim (Thm.cterm_of ctxt a);
val impI_BA     = impI_at B A;
val impI_AimpBA = impI_at A (mkimp B A);
val cA = Thm.cterm_of ctxt (jT A); val cB = Thm.cterm_of ctxt (jT B);
val premBA = Thm.implies_intr cB (Thm.assume cA);
val innerK = Thm.implies_elim impI_BA premBA;
val premAimpBA = Thm.implies_intr cA innerK;
val thmK_kernel = Thm.implies_elim impI_AimpBA premAimpBA;

(* K via tactic *)
val goalK = jT (mkimp A (mkimp B A));
val thmK = Goal.prove ctxt [] [] goalK
  (fn _ => resolve_tac ctxt [impI_r] 1 THEN resolve_tac ctxt [impI_r] 1 THEN assume_tac ctxt 1);

(* S via tactic: peel 3 imps, then chain mp eliminations *)
val goalS = jT (mkimp (mkimp A (mkimp B C)) (mkimp (mkimp A B) (mkimp A C)));
val thmS = Goal.prove ctxt [] [] goalS
  (fn _ => resolve_tac ctxt [impI_r] 1 THEN resolve_tac ctxt [impI_r] 1 THEN resolve_tac ctxt [impI_r] 1
           THEN REPEAT (assume_tac ctxt 1 ORELSE resolve_tac ctxt [mp_r] 1));

val okK_k = (Thm.prop_of thmK_kernel = goalK) andalso null (Thm.hyps_of thmK_kernel) andalso Thm.nprems_of thmK_kernel = 0;
val okK_t = (Thm.prop_of thmK = goalK) andalso null (Thm.hyps_of thmK) andalso Thm.nprems_of thmK = 0;
val okS   = (Thm.prop_of thmS = goalS) andalso null (Thm.hyps_of thmS) andalso Thm.nprems_of thmS = 0;
val () = out ("K (kernel): " ^ Thm.string_of_thm ctxt thmK_kernel ^ "\n");
val () = out ("K (tactic): " ^ Thm.string_of_thm ctxt thmK ^ "\n");
val () = out ("S (tactic): " ^ Thm.string_of_thm ctxt thmS ^ "\n");
val () = out (if okK_k andalso okK_t andalso okS then "ALL_OK\n" else "SOME_FAIL\n");
in val () = out ("RUNG oimp " ^ (if okK_k andalso okK_t andalso okS then "OK" else "FAIL") ^ " :: " ^ Thm.string_of_thm ctxt thmK ^ "\n") end;

(* ===== disj ===== *)
local

(* ---- Build the object logic on bare Pure ---- *)
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global [(Binding.name "o", 0, NoSyn)] thy0;
val oT = Type (Sign.intern_type thy1 "o", []);

val thy2 = Sign.add_consts
  [ (Binding.name "Trueprop", oT --> propT, NoSyn),
    (Binding.name "disj", oT --> oT --> oT, NoSyn) ] thy1;

val disjC = Const (Sign.intern_const thy2 "disj", oT --> oT --> oT);
val TP    = Const (Sign.intern_const thy2 "Trueprop", oT --> propT);
fun tp t = TP $ t;
fun mkdisj a b = disjC $ a $ b;
val A = Free ("A", oT); val B = Free ("B", oT); val C = Free ("C", oT);

(* ---- Axioms (with Free A,B,C) ---- *)
val disjI1_prop = Logic.mk_implies (tp A, tp (mkdisj A B));
val disjI2_prop = Logic.mk_implies (tp B, tp (mkdisj A B));
val disjE_prop =
  Logic.mk_implies (tp (mkdisj A B),
    Logic.mk_implies (Logic.mk_implies (tp A, tp C),
      Logic.mk_implies (Logic.mk_implies (tp B, tp C), tp C)));

val ((_, disjI1_0), thy3) = Thm.add_axiom_global (Binding.name "disjI1", disjI1_prop) thy2;
val ((_, disjI2_0), thy4) = Thm.add_axiom_global (Binding.name "disjI2", disjI2_prop) thy3;
val ((_, disjE_0),  thy5) = Thm.add_axiom_global (Binding.name "disjE",  disjE_prop)  thy4;

val ctxt = Proof_Context.init_global thy5;

(* Generalize the Free formula vars A,B,C into SCHEMATIC vars so resolution unifies *)
val gen = Drule.generalize
  (Names.empty, Names.build (Names.add_set "A" #> Names.add_set "B" #> Names.add_set "C"));
val disjI1 = Drule.zero_var_indexes (gen disjI1_0);
val disjI2 = Drule.zero_var_indexes (gen disjI2_0);
val disjE  = Drule.zero_var_indexes (gen disjE_0);

val () = out ("AX disjI1: " ^ Thm.string_of_thm ctxt disjI1 ^ "\n");
val () = out ("AX disjI2: " ^ Thm.string_of_thm ctxt disjI2 ^ "\n");
val () = out ("AX disjE : " ^ Thm.string_of_thm ctxt disjE  ^ "\n");

(* ---- GOAL: disj A B ==> disj B A ---- (A,B stay Free in the goal) *)
val goal = Logic.mk_implies (tp (mkdisj A B), tp (mkdisj B A));
val () = out ("GOAL: " ^ Syntax.string_of_term ctxt goal ^ "\n");

(* Proof:
   eresolve disjE: consumes the assumption `disj A B`, leaving two cases:
     1. A ==> disj B A     (resolve disjI2 X==>disj Y X: Y:=B,X:=A; premise A; assume_tac)
     2. B ==> disj B A     (resolve disjI1 X==>disj X Y: X:=B,Y:=A; premise B; assume_tac) *)
val tac =
  eresolve_tac ctxt [disjE] 1
  THEN resolve_tac ctxt [disjI2] 1
  THEN assume_tac ctxt 1
  THEN resolve_tac ctxt [disjI1] 1
  THEN assume_tac ctxt 1;

val th = Goal.prove ctxt [] [] goal (fn _ => tac);

val () = out ("THM: " ^ Thm.string_of_thm ctxt th ^ "\n");
val () = out ("NHYPS: " ^ Int.toString (length (Thm.hyps_of th)) ^ "\n");
val () = out ("PROP-eq-goal: " ^ Bool.toString (Thm.prop_of th aconv goal) ^ "\n");
val concl = Logic.strip_imp_concl (Thm.prop_of th);
val () = out ("CONCL: " ^ Syntax.string_of_term ctxt concl ^ "\n");
val () = out ("OK disjunction commutativity proved\n");
in val () = out ("RUNG disj " ^ (if (Thm.prop_of th aconv goal) andalso null (Thm.hyps_of th) then "OK" else "FAIL") ^ " :: " ^ Thm.string_of_thm ctxt th ^ "\n") end;

(* ===== forall ===== *)
local
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global [(Binding.name "o", 0, NoSyn), (Binding.name "i", 0, NoSyn)] thy0;
val oName = Sign.intern_type thy1 "o";
val iName = Sign.intern_type thy1 "i";
val oT  = Type (oName, []);
val iT  = Type (iName, []);
val predT = iT --> oT;
val thy2 = Sign.add_consts [ (Binding.name "Trueprop", oT --> propT, NoSyn), (Binding.name "conj", oT --> oT --> oT, NoSyn), (Binding.name "All", predT --> oT, NoSyn) ] thy1;
fun full thy nm = Sign.intern_const thy nm;
val tp_c   = Const (full thy2 "Trueprop", oT --> propT);
val conj_c = Const (full thy2 "conj", oT --> oT --> oT);
val all_c  = Const (full thy2 "All", predT --> oT);
fun T phi = tp_c $ phi;
fun mkconj a b = conj_c $ a $ b;
fun mkall pr = all_c $ pr;
val A = Free ("A", oT);
val B = Free ("B", oT);
val conjI_prop = Logic.mk_implies (T A, Logic.mk_implies (T B, T (mkconj A B)));
val ((_, conjI), thy3) = Thm.add_axiom_global (Binding.name "conjI", conjI_prop) thy2;
val conjunct1_prop = Logic.mk_implies (T (mkconj A B), T A);
val ((_, conjunct1), thy4) = Thm.add_axiom_global (Binding.name "conjunct1", conjunct1_prop) thy3;
val P = Free ("P", predT);
val x = Free ("x", iT);
val allI_prop = Logic.mk_implies (Logic.all x (T (P $ x)), T (mkall P));
val ((_, allI), thy5) = Thm.add_axiom_global (Binding.name "allI", allI_prop) thy4;
val a = Free ("a", iT);
val spec_prop = Logic.mk_implies (T (mkall P), T (P $ a));
val ((_, spec), thy6) = Thm.add_axiom_global (Binding.name "spec", spec_prop) thy5;
val thy = thy6;
val ctxt = Proof_Context.init_global thy;
fun schematic rule = let val frees = Names.build (rule |> Thm.fold_terms {hyps = true} Names.add_free_names) in rule |> Thm.generalize (Names.empty, frees) 1 |> Drule.zero_var_indexes end;
val conjI'     = schematic conjI;
val conjunct1' = schematic conjunct1;
val allI'      = schematic allI;
val spec'      = schematic spec;
val Pp = Free ("P", predT);
val Qp = Free ("Q", predT);
val PQ = Abs ("x", iT, mkconj (Pp $ Bound 0) (Qp $ Bound 0));
val premise   = T (mkall PQ);
val conclusion = T (mkall Pp);
val goal = Logic.mk_implies (premise, conclusion);
val th = Goal.prove ctxt [] [premise] conclusion (fn {context = c, prems} => let val prem = hd prems; val spec_prem = Conv.fconv_rule (Thm.beta_conversion true) (spec' OF [prem]); val pa = conjunct1' OF [spec_prem] in resolve_tac c [allI'] 1 THEN resolve_tac c [pa] 1 end);
val nhyps = length (Thm.hyps_of th);
val ok_shape = (Thm.prop_of th aconv goal);
val verified = (nhyps = 0) andalso ok_shape;
in val () = out ("RUNG forall " ^ (if verified then "OK" else "FAIL") ^ " :: " ^ Thm.string_of_thm ctxt th ^ "\n") end;

(* ===== oeq ===== *)
local

(* Build object-logic theory: types o,i; consts Trueprop,oeq; axioms refl,subst *)
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global
  [(Binding.name "o", 0, NoSyn), (Binding.name "i", 0, NoSyn)] thy0;
(* draft theory qualifies type names as ??.Pure.o -- resolve real names *)
val oName = Sign.full_name thy1 (Binding.name "o");
val iName = Sign.full_name thy1 (Binding.name "i");
val oT = Type (oName, []);
val iT = Type (iName, []);
(* NB: "eq" collides with Pure.eq (meta ==), so object equality is "oeq" *)
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "oeq", iT --> iT --> oT, NoSyn)] thy1;
val truepropName = Sign.full_name thy2 (Binding.name "Trueprop");
val eqName = Sign.full_name thy2 (Binding.name "oeq");
fun Trueprop t = Const (truepropName, oT --> propT) $ t;
val eqC = Const (eqName, iT --> iT --> oT);
fun mkEq (s, t) = eqC $ s $ t;
val a = Free ("a", iT);
val b = Free ("b", iT);
val refl_prop = Trueprop (mkEq (a, a));
val P = Free ("P", iT --> oT);
val subst_prop =
  Logic.mk_implies
    (Trueprop (mkEq (a, b)),
     Logic.mk_implies (Trueprop (P $ a), Trueprop (P $ b)));
val ((_, refl_thm), thy3) =
  Thm.add_axiom_global (Binding.name "oeq_refl", refl_prop) thy2;
val ((_, subst_thm), thy4) =
  Thm.add_axiom_global (Binding.name "oeq_subst", subst_prop) thy3;
val thy = thy4;
val ctxt = Proof_Context.init_global thy;

(* Prove SYMMETRY: oeq a b ==> oeq b a *)
(* CRUX: subst's predicate must be a function term P :: i=>o, supplied as an Abs *)
val Ppred = Abs ("x", iT, mkEq (Bound 0, a));   (* %x. oeq x a : i=>o *)
(* add_axiom_global keeps Frees (no Vars) -> infer_instantiate cannot bind;
   lift Free P to !!P then forall_elim at Ppred *)
val cP     = Thm.cterm_of ctxt P;
val cPpred = Thm.cterm_of ctxt Ppred;
val subst_gen   = Thm.forall_intr cP subst_thm;
val subst_inst0 = Thm.forall_elim cPpred subst_gen;
(* forall_elim does NOT beta-reduce; kernel implies_elim checks aconv not beta;
   so beta-normalise the whole thm before resolving *)
fun beta_norm th =
  Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;
val subst_inst = beta_norm subst_inst0;  (* oeq a b ==> oeq a a ==> oeq b a *)
val refl_at_a = refl_thm;                (* already oeq a a at Free a *)
val cprem1 = Thm.cprem_of subst_inst 1;
val h_ab   = Thm.assume cprem1;                    (* oeq a b |- oeq a b *)
val step1  = Thm.implies_elim subst_inst h_ab;     (* oeq a b |- oeq a a ==> oeq b a *)
val step2  = Thm.implies_elim step1 refl_at_a;     (* oeq a b |- oeq b a *)
val sym_thm = Thm.implies_intr cprem1 step2;       (* |- oeq a b ==> oeq b a *)

val () = out ("THM symmetry: " ^ Thm.string_of_thm ctxt sym_thm ^ "\n");
val nhyps = length (Thm.hyps_of sym_thm);
val expected = Logic.mk_implies (Trueprop (mkEq (a, b)), Trueprop (mkEq (b, a)));
val structOk = (Thm.prop_of sym_thm) aconv expected;
val () =
  if nhyps = 0 andalso structOk
  then out "RESULT OK: oeq a b ==> oeq b a is a checked Isabelle theorem (0 hyps)\n"
  else out "RESULT FAIL\n";
(* Saved driver: /tmp/ol_equality.sml ; output: /tmp/ol_equality.out *)
in val () = out ("RUNG oeq " ^ (if structOk andalso null (Thm.hyps_of sym_thm) then "OK" else "FAIL") ^ " :: " ^ Thm.string_of_thm ctxt sym_thm ^ "\n") end;

val () = out "ISA_OBJLOGIC_DONE\n";
