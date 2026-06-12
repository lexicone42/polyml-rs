(* isabelle_proving.sml — REAL ISABELLE PROVING on the warm /tmp/isabelle_pure
   checkpoint (the loaded logical Pure), all on the Rust PolyML interpreter.

   This is the Isabelle analogue of the HOL4 verified-programs arc: now that the
   logical Pure loads (kernel + Isar + proof + method + simplifier + syntax), we
   exercise its proving machinery and check that each produces a genuine `thm`.

   Five rungs, each a CHECKED Isabelle/Pure theorem:
     1. TACTIC FRAMEWORK   Goal.prove + resolve_tac/assume_tac  ⊢ PROP A ⟹ PROP A
     2. SIMPLIFIER         Simplifier.rewrite (beta) + asm_full_simp_tac
                           ⊢ (f c ≡ d) ⟹ g (f c) ≡ g d   (assumption-driven congruence)
     3. THEORY + AXIOM     declare a type/consts, state ⋀x. P x, derive  ⊢ P c
     4. RESOLUTION/DRULE   RS + implies_intr_list  ⊢ (A⟹B) ⟹ (B⟹C) ⟹ A ⟹ C
     5. PARSER             Syntax.read_prop "PROP A ==> PROP A" → ⊢ PROP A ⟹ PROP A

   Found by a 5-seat ultracode workflow (wf_e7312cf7-ece); all five verified.

   CHECKPOINT IDIOMS: the REPL namespace is ISABELLE ML (no `print`); use `out`
   (TextIO). The generic context is thread-local and lost on reload, so the FIRST
   line is `restore_pure_context ()` (captured in the checkpoint build). The
   proto-Pure theory is bare meta-logic (Pure.eq/imp/all), so declare fun/prop
   types before building typed terms.

   Run: poly run /tmp/isabelle_pure < this file *)

val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
val () = out "ISA_PROVING_START\n";

(* base theory with fun/prop declared, shared shape across rungs *)
fun baseThy () =
  Sign.add_types_global
    [(Binding.name "fun", 2, NoSyn), (Binding.name "prop", 0, NoSyn)]
    (Context.the_global_context ());

(* ===== RUNG 1: the TACTIC FRAMEWORK (Goal.prove) ===== *)
local
  val thy = baseThy ();
  val ctxt = Proof_Context.init_global thy;
  val propT = Type ("prop", []);
  val tA = Free ("A", propT);
  val goal = Logic.mk_implies (tA, tA);                 (* A ==> A *)
  val cA = Thm.global_cterm_of thy tA;
  (* resolve with the trivial rule A==>A, then discharge by assumption *)
  val th = Goal.prove ctxt [] [] goal
             (fn _ => resolve_tac ctxt [Thm.trivial cA] 1 THEN assume_tac ctxt 1);
  val ok = Thm.nprems_of th = 1 andalso null (Thm.hyps_of th) andalso
           (case Thm.prop_of th of
              (Const ("Pure.imp", _) $ Free ("A", _)) $ Free ("A", _) => true | _ => false);
in val () = out ("RUNG tactic " ^ (if ok then "OK" else "FAIL")
                 ^ " :: " ^ Thm.string_of_thm ctxt th ^ "\n") end;

(* ===== RUNG 2: the SIMPLIFIER ===== *)
local
  val thy = baseThy ();
  val ctxt = Proof_Context.init_global thy;
  val aT = TFree ("a", []);
  val c = Free ("c", aT);
  val fT = aT --> aT;
  val f = Free ("f", fT); val g = Free ("g", fT); val d = Free ("d", aT);
  val idf = Abs ("x", aT, Bound 0);                     (* (%x. x) *)
  val ssE = Simplifier.empty_simpset ctxt;
  (* (a) Simplifier.rewrite as a conv: |- (%x. x) c == c  (beta) *)
  val rw_beta = Simplifier.rewrite ssE (Thm.global_cterm_of thy (idf $ c));
  (* (b) Goal.prove + asm_full_simp_tac: real congruence using the premise *)
  val goalB = Logic.mk_implies (Logic.mk_equals (f $ c, d),
                                Logic.mk_equals (g $ (f $ c), g $ d));
  val thB = Goal.prove ctxt [] [] goalB
              (fn _ => Simplifier.asm_full_simp_tac ssE 1
                       THEN REPEAT (resolve_tac ctxt [Drule.reflexive_thm] 1));
  val ok = null (Thm.hyps_of rw_beta) andalso null (Thm.hyps_of thB)
           andalso Thm.nprems_of thB = 1;
in val () = out ("RUNG simplifier " ^ (if ok then "OK" else "FAIL")
                 ^ " :: " ^ Thm.string_of_thm ctxt thB ^ "\n") end;

(* ===== RUNG 3: THEORY DEVELOPMENT (declare + axiom + derive) ===== *)
local
  val thy1 = Sign.add_types_global
    [(Binding.name "fun", 2, NoSyn), (Binding.name "prop", 0, NoSyn),
     (Binding.name "nat", 0, NoSyn)] (Context.the_global_context ());
  val natName = Sign.full_name thy1 (Binding.name "nat");
  val propT = Type ("prop", []);
  val natT = Type (natName, []);
  val predT = natT --> propT;
  val thy2 = Sign.add_consts
    [(Binding.name "P", predT, NoSyn), (Binding.name "c", natT, NoSyn)] thy1;
  val pName = Sign.full_name thy2 (Binding.name "P");
  val cName = Sign.full_name thy2 (Binding.name "c");
  val Pconst = Const (pName, predT);
  val Cconst = Const (cName, natT);
  (* state the axiom  !!x. P x  and retrieve it as a thm *)
  val axProp = Logic.all (Free ("x", natT)) (Pconst $ Free ("x", natT));
  val ((_, axThm), thy3) = Thm.add_axiom_global (Binding.name "ax1", axProp) thy2;
  (* derive  P c  by forall_elim of the axiom — genuinely USES the axiom *)
  val derived = Thm.forall_elim (Thm.global_cterm_of thy3 Cconst) axThm;
  val ctxt3 = Proof_Context.init_global thy3;
  val ok = null (Thm.hyps_of derived) andalso
           (case Thm.prop_of derived of
              Const (n, _) $ Const (m, _) => n = pName andalso m = cName | _ => false);
in val () = out ("RUNG theory_axiom " ^ (if ok then "OK" else "FAIL")
                 ^ " :: " ^ Thm.string_of_thm ctxt3 derived ^ "\n") end;

(* ===== RUNG 4: RESOLUTION / Drule ===== *)
local
  val thy = baseThy ();
  val ctxt = Proof_Context.init_global thy;
  val propT = Type ("prop", []);
  fun ct t = Thm.global_cterm_of thy t;
  val A = Free ("A", propT); val B = Free ("B", propT); val C = Free ("C", propT);
  val cAB = ct (Logic.mk_implies (A, B));
  val cBC = ct (Logic.mk_implies (B, C));
  val thAB = Thm.assume cAB;
  val thBC = Thm.assume cBC;
  val chained = thAB RS thBC;                           (* A==>B, B==>C |- A==>C *)
  val transImp = Drule.implies_intr_list [cAB, cBC] chained;  (* the closed rule *)
  val ok = null (Thm.hyps_of transImp) andalso Thm.nprems_of transImp = 3 andalso
    (case Thm.prop_of transImp of
       (Const ("Pure.imp", _) $ ((Const ("Pure.imp", _) $ Free ("A", _)) $ Free ("B", _)))
         $ ((Const ("Pure.imp", _) $ ((Const ("Pure.imp", _) $ Free ("B", _)) $ Free ("C", _)))
              $ ((Const ("Pure.imp", _) $ Free ("A", _)) $ Free ("C", _))) => true
     | _ => false);
in val () = out ("RUNG resolution " ^ (if ok then "OK" else "FAIL")
                 ^ " :: " ^ Thm.string_of_thm ctxt transImp ^ "\n") end;

(* ===== RUNG 5: the PARSER (Syntax.read_prop) ===== *)
local
  val ctxt0 = Proof_Context.init_global (Context.the_global_context ());
  val prop = Syntax.read_prop ctxt0 "PROP A ==> PROP A";  (* parse from a STRING *)
  val cprop = Thm.cterm_of ctxt0 prop;
  val (cA, _) = Thm.dest_implies cprop;
  val th = Thm.implies_intr cA (Thm.assume cA);           (* |- A ==> A *)
  val ok = (Thm.prop_of th = prop) andalso null (Thm.hyps_of th)
           andalso Thm.nprems_of th = 1;
in val () = out ("RUNG parser " ^ (if ok then "OK" else "FAIL")
                 ^ " :: " ^ Thm.string_of_thm ctxt0 th ^ "\n") end;

val () = out "ISA_PROVING_DONE\n";
