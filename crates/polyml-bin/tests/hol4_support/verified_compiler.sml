(* verified_compiler.sml — a VERIFIED COMPILER on HOL4's real LCF kernel,
   running on the Rust PolyML interpreter (/tmp/hol4_datatype). The classic
   Bahr-Hutton result and the crown jewel of formal methods: compile an
   arithmetic-expression language to a stack machine and PROVE the compiler
   correct.

     SOURCE  expr  = Const num | Plus expr expr | Times expr expr   (eval : expr -> num)
     TARGET  instr = Push num | Add | Mul                           (one instruction)
             code  = CNil | CCons instr code                        (instruction list)
             stack = SNil | SPush num stack                         (the machine stack)
     compile : expr -> code        exec : code -> stack -> stack

     HEADLINE  compile_correct : |- !e s. exec (compile e) s = SPush (eval e) s
       (running the compiled code on ANY stack pushes exactly the value the
        source evaluates to — a ZERO-hypothesis theorem)

   The proof is structural induction on e (the expr induction theorem from
   TypeBase), resting on the distributivity lemma
     exec_capp : |- !xs ys s. exec (capp xs ys) s = exec ys (exec xs s)
   (exec over concatenated code, by induction on the code xs). Engineered by a
   3-seat ultracode fleet (wf_a9867385-1d0); all three seats verified
   independently, all with the EVAL demo.

   /tmp/hol4_datatype has NO listTheory (no :: / [] / :num list), so every
   list-like type (code, stack) is defined here via Datatype.Datatype — fully
   self-contained, the same pattern as insertion_sort_verified.sml.

   THREE non-obvious things this file gets right (see inline comments):
   1. CONTINUE-ON-UNDERFLOW, not short-circuit. The exec underflow catch-alls
      are `exec (CCons Add is) s = exec is s` (skip the op, recurse on the
      tail), NOT `= s` (stop). The short-circuit form makes exec_capp LITERALLY
      FALSE — a shallow stack stops the LHS mid-stream while the RHS keeps
      running ys (counterexample: xs=[Add], ys=[Push 9], s=SNil). Continue-on-
      underflow keeps exec fold-like over the code list so it distributes over
      capp, and leaves compile_correct valid (compiled code never underflows).
   2. exec needs tDefine (not Define): the recursion decreases the code but the
      stack changes shape, defeating Define's measure guesser. WF_REL_TAC
      `measure (code_size o FST)` + SIMP with measure_thm/o_THM/FST/code_size_def.
      tDefine returns (thm, thm option) — destructure `val (exec,_) = ...`.
   3. The stack/instr case splits use STRUCT_CASES_TAC over the TypeBase
      nchotomy theorems (the BasicProvers Cases_on shim here only handles
      bool/num). For Add/Mul, exec only reduces once the stack is split to
      depth 2 (SNil / SPush v SNil / SPush b (SPush a s)).

   The EVAL bonus RUNS a Times program (2 + 3*4 = 14) through the computeLib
   call-by-value engine: the compiled code executes on the stack machine to
   SPush 14 SNil and the source eval agrees (14). numeral MULTIPLICATION now
   reduces in computeLib — the datatype-checkpoint build repairs the
   numeral-mult compset rules (the numeral sweep had banked degraded DB
   theorems; build_datatype_checkpoint.sml re-adds the correct structure-value
   numeralTheory.numeral_mult family). (reduceLib.REDUCE_CONV still stalls on *
   — a separate baked compset — so the EVAL uses computeLib CBV, not REDUCE.)

   OPTIMIZING-COMPILER EXTENSION (appended below, after compile_correct):
   a constant-folding source-to-source OPTIMIZER `simplify` is defined and
   proved semantics-preserving, then COMPOSED with the compiler — the CompCert
   pattern of composing two independently-verified passes:
     simplify_correct    : |- !e. eval (simplify e) = eval e
     opt_compile_correct : |- !e s. exec (compile (simplify e)) s = SPush (eval e) s
   The composition is a 2-line corollary (REWRITE[compile_correct,
   simplify_correct]); neither proof re-opens the other's internals.

   Run: tools/sml-exp.sh /tmp/hol4_datatype \
          crates/polyml-bin/tests/hol4_support/verified_compiler.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL ORELSE;
open boolLib;

(* ---- SOURCE language ---- *)
Datatype.Datatype [QUOTE "expr = Const num | Plus expr expr | Times expr expr"];
pr "OK datatype expr\n";

val eval = TotalDefn.Define [QUOTE
  "(eval (Const n) = n) /\\ (eval (Plus a b) = eval a + eval b) /\\ (eval (Times a b) = eval a * eval b)"];
pr "OK eval\n";

(* ---- TARGET ---- *)
Datatype.Datatype [QUOTE "instr = Push num | Add | Mul"];
pr "OK datatype instr\n";
Datatype.Datatype [QUOTE "code = CNil | CCons instr code"];
pr "OK datatype code\n";
Datatype.Datatype [QUOTE "stack = SNil | SPush num stack"];
pr "OK datatype stack\n";

(* ---- code concatenation ---- *)
val capp = TotalDefn.Define [QUOTE
  "(capp CNil ys = ys) /\\ (capp (CCons x xs) ys = CCons x (capp xs ys))"];
pr "OK capp\n";

(* ---- compiler ---- *)
val compile = TotalDefn.Define [QUOTE
  "(compile (Const n) = CCons (Push n) CNil) /\\ (compile (Plus a b) = capp (compile a) (capp (compile b) (CCons Add CNil))) /\\ (compile (Times a b) = capp (compile a) (capp (compile b) (CCons Mul CNil)))"];
pr "OK compile\n";

(* size def for code (needed to discharge exec's termination) *)
val SOME code_tyi_pre = TypeBase.fetch (Type.mk_thy_type
  {Thy=Theory.current_theory(), Tyop="code", Args=[]});
val SOME (_, code_size_def) = TypeBasePure.size_of code_tyi_pre;
pr "OK code_size_def\n";

(* ---- stack-machine execution (overlapping rows) ----
   NOTE: the underflow catch-alls CONTINUE executing the tail (exec is s),
   they do NOT short-circuit (exec ... s = s). The short-circuit form makes
   the key lemma exec_capp FALSE (a shallow stack stops LHS but RHS keeps
   running ys). Continue-on-underflow keeps exec fold-like over the code
   list so it distributes over capp, and leaves compile_correct valid since
   compiled code never underflows. *)
val (exec, _) = TotalDefn.tDefine "exec" [QUOTE
  "(exec CNil s = s) /\\ (exec (CCons (Push n) is) s = exec is (SPush n s)) /\\ (exec (CCons Add is) (SPush b (SPush a s)) = exec is (SPush (a + b) s)) /\\ (exec (CCons Add is) s = exec is s) /\\ (exec (CCons Mul is) (SPush b (SPush a s)) = exec is (SPush (a * b) s)) /\\ (exec (CCons Mul is) s = exec is s)"]
  (Tactical.THEN (TotalDefn.WF_REL_TAC [QUOTE "measure (code_size o FST)"],
     simpLib.SIMP_TAC (simpLib.++(boolSimps.bool_ss, numSimps.ARITH_ss))
       [prim_recTheory.measure_thm, combinTheory.o_THM, pairTheory.FST, code_size_def]))
  handle e => (pr ("EXEC DEFINE FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK exec\n";

(* ---- fetch induction theorems ---- *)
val SOME expr_tyi = TypeBase.fetch (Type.mk_thy_type
  {Thy=Theory.current_theory(), Tyop="expr", Args=[]});
val expr_ind = TypeBasePure.induction_of expr_tyi;
val SOME code_tyi = TypeBase.fetch (Type.mk_thy_type
  {Thy=Theory.current_theory(), Tyop="code", Args=[]});
val code_ind = TypeBasePure.induction_of code_tyi;
val SOME instr_tyi = TypeBase.fetch (Type.mk_thy_type
  {Thy=Theory.current_theory(), Tyop="instr", Args=[]});
val instr_nchot = TypeBasePure.nchotomy_of instr_tyi;
val SOME stack_tyi = TypeBase.fetch (Type.mk_thy_type
  {Thy=Theory.current_theory(), Tyop="stack", Args=[]});
val stack_nchot = TypeBasePure.nchotomy_of stack_tyi;
pr "OK fetch inductions\n";

fun byInd ind tac = Tactical.THEN (Tactic.HO_MATCH_MP_TAC ind,
    Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));

(* split the head instr i into Push/Add/Mul *)
val splitI = Tactic.STRUCT_CASES_TAC
  (Drule.ISPEC (Parse.Term [QUOTE "i:instr"]) instr_nchot);
(* split a stack-typed variable into SNil / SPush v <fresh>.  HOL4 names the
   fresh tail s' (and the next level s''), deterministically. *)
fun splitStack v = Tactic.STRUCT_CASES_TAC
  (Drule.ISPEC (Parse.Term [QUOTE (v ^ ":stack")]) stack_nchot);

(* ---- KEY LEMMA: exec distributes over capp ----
   Induction on the code xs.  In the step case rewrite capp, then split the
   head instr; for Add/Mul the exec clauses fire only once the stack is split
   to depth 2 (SNil / SPush v SNil / SPush b (SPush a s)).  After that every
   branch is exactly the inductive hypothesis (in the assumptions), so
   ASM_REWRITE[exec] closes it.  The two-level stack split is TRY-guarded so it
   is a harmless no-op on the Push case and on the shallow Add/Mul branches. *)
val stepTac =
  Tactical.THEN (Rewrite.ASM_REWRITE_TAC [capp, exec],   (* closes CNil base; unfolds capp in step *)
    Tactical.TRY (                                        (* step case only: head instr present *)
      Tactical.THEN (splitI,
        Tactical.THEN (
          Tactical.TRY (Tactical.THEN (splitStack "s",
                          Tactical.TRY (splitStack "s'"))),
          Rewrite.ASM_REWRITE_TAC [exec]))));

val exec_capp = Tactical.prove(
  Parse.Term [QUOTE "!xs ys s. exec (capp xs ys) s = exec ys (exec xs s)"],
  byInd code_ind stepTac
  ) handle e => (pr ("EXEC_CAPP FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK exec_capp\n";

(* ---- HEADLINE: compiler correct ---- *)
val compile_correct = Tactical.prove(
  Parse.Term [QUOTE "!e s. exec (compile e) s = SPush (eval e) s"],
  byInd expr_ind (
    Tactical.THEN (Rewrite.REWRITE_TAC [compile],
      Tactical.THEN (Rewrite.REWRITE_TAC [exec_capp],
        Rewrite.ASM_REWRITE_TAC [exec, eval])))
  );
pr "OK compile_correct\n";

pr "THEOREM: ";
pr (Parse.thm_to_string compile_correct);
pr "\n";

(* assert ZERO hypotheses *)
val nhyp = length (Thm.hyp compile_correct);
pr ("NHYP = " ^ Int.toString nhyp ^ "\n");
val () = if nhyp = 0 then pr "ZERO_HYP_OK\n" else pr "HAS HYPOTHESES!\n";

(* ---- BONUS: actually RUN a concrete compiled program and check it agrees
   with eval, including MULTIPLICATION.  We use the call-by-value computeLib
   engine over the global compset (copied + the function defs added), which on
   this checkpoint reduces numeral * as well as + (the build repairs the
   numeral-mult compset rules — see build_datatype_checkpoint.sml).  The program
       Plus (Const 2) (Times (Const 3) (Const 4))     -- eval = 2 + 3*4 = 14
   exercises Push + Add + Mul + code concatenation; the compiled code runs on
   the stack machine to SPush 14 SNil and the source eval agrees (14), both
   kernel-checked equalities. *)
val () = (
  let
    val cs = computeLib.copy (!computeLib.the_compset);
    val _ = computeLib.add_thms [compile, capp, exec, eval] cs;
    val prog = "Plus (Const 2) (Times (Const 3) (Const 4))"
    val machine = computeLib.CBV_CONV cs (Parse.Term [QUOTE ("exec (compile (" ^ prog ^ ")) SNil")])
    val source  = computeLib.CBV_CONV cs (Parse.Term [QUOTE ("eval (" ^ prog ^ ")")])
    val mrhs = boolSyntax.rhs (Thm.concl machine)
    val srhs = boolSyntax.rhs (Thm.concl source)
  in
    pr ("EVAL machine run: " ^ Parse.term_to_string mrhs ^ "\n");
    pr ("EVAL source eval: " ^ Parse.term_to_string srhs ^ "\n");
    if Term.aconv mrhs (Parse.Term [QUOTE "SPush 14 SNil"])
       andalso Term.aconv srhs (Parse.Term [QUOTE "14"])
    then pr "EVAL_OK\n"
    else pr "EVAL_WRONG\n"
  end
) handle e => pr ("EVAL FAILED: " ^ General.exnMessage e ^ "\n");

(* ================================================================== *)
(* === OPTIMIZING COMPILER: a constant-folding source-to-source     === *)
(* === optimizer (simplify), proved semantics-preserving, and       === *)
(* === COMPOSED with the verified compiler above (CompCert-style):   === *)
(* ===   simplify_correct    : |- !e. eval (simplify e) = eval e     === *)
(* ===   opt_compile_correct : |- !e s. exec (compile (simplify e)) s === *)
(* ===                                  = SPush (eval e) s           === *)
(* === The composition is a 2-line corollary of compile_correct +    === *)
(* === simplify_correct — neither proof re-opens the other.          === *)
(* === (3-seat fleet wf_b7e907bb-345; all 3 verified + EVAL.)        === *)
(* ================================================================== *)
(* ===== NEW CODE: constant-folding optimizer + correctness + composition ===== *)

(* nchotomy for expr (to case-split arguments of mkPlus/mkTimes) *)
val expr_nchot = TypeBasePure.nchotomy_of expr_tyi;

(* (a) smart constructors that fold constant subterms.
   The Const/Const row is FIRST so first-match folds constants;
   the catch-all (Plus/Times) fires otherwise. Non-recursive. *)
val mkPlus = TotalDefn.Define [QUOTE
  "(mkPlus (Const m) (Const n) = Const (m + n)) /\\ (mkPlus a b = Plus a b)"];
pr "OK mkPlus\n";

val mkTimes = TotalDefn.Define [QUOTE
  "(mkTimes (Const m) (Const n) = Const (m * n)) /\\ (mkTimes a b = Times a b)"];
pr "OK mkTimes\n";

(* simplify recurses structurally on expr *)
val simplify = TotalDefn.Define [QUOTE
  "(simplify (Const n) = Const n) /\\ (simplify (Plus a b) = mkPlus (simplify a) (simplify b)) /\\ (simplify (Times a b) = mkTimes (simplify a) (simplify b))"];
pr "OK simplify\n";

(* case-split a:expr / b:expr via the expr nchotomy *)
fun splitExpr v = Tactic.STRUCT_CASES_TAC
  (Drule.ISPEC (Parse.Term [QUOTE (v ^ ":expr")]) expr_nchot);

(* ---- mkPlus_correct : !a b. eval (mkPlus a b) = eval a + eval b ----
   Split a then b over the expr nchotomy. Only Const/Const folds specially;
   every other branch hits the catch-all mkPlus a b = Plus a b. In all 9
   cases REWRITE[mkPlus, eval] closes the goal (the Const/Const case
   reduces eval (Const (m+n)) = m + n = eval(Const m)+eval(Const n)). *)
val mkPlus_correct = Tactical.prove(
  Parse.Term [QUOTE "!a b. eval (mkPlus a b) = eval a + eval b"],
  Tactical.THEN (Tactic.GEN_TAC,
    Tactical.THEN (splitExpr "a",
      Tactical.THEN (Tactic.GEN_TAC,
        Tactical.THEN (splitExpr "b",
          Rewrite.REWRITE_TAC [mkPlus, eval]))))
  ) handle e => (pr ("MKPLUS_CORRECT FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK mkPlus_correct\n";

(* ---- mkTimes_correct : !a b. eval (mkTimes a b) = eval a * eval b ---- *)
val mkTimes_correct = Tactical.prove(
  Parse.Term [QUOTE "!a b. eval (mkTimes a b) = eval a * eval b"],
  Tactical.THEN (Tactic.GEN_TAC,
    Tactical.THEN (splitExpr "a",
      Tactical.THEN (Tactic.GEN_TAC,
        Tactical.THEN (splitExpr "b",
          Rewrite.REWRITE_TAC [mkTimes, eval]))))
  ) handle e => (pr ("MKTIMES_CORRECT FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK mkTimes_correct\n";

(* ---- (b) HEADLINE 1: simplify_correct : !e. eval (simplify e) = eval e ----
   expr induction. Const: REWRITE[simplify, eval]. Plus/Times: REWRITE[simplify]
   then mkPlus_correct/mkTimes_correct then ASM_REWRITE[eval] with the two IHs. *)
val simplify_correct = Tactical.prove(
  Parse.Term [QUOTE "!e. eval (simplify e) = eval e"],
  byInd expr_ind (
    Tactical.THEN (Rewrite.REWRITE_TAC [simplify, mkPlus_correct, mkTimes_correct],
      Rewrite.ASM_REWRITE_TAC [eval]))
  ) handle e => (pr ("SIMPLIFY_CORRECT FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK simplify_correct\n";

pr "THEOREM simplify_correct: ";
pr (Parse.thm_to_string simplify_correct);
pr "\n";
val nhyp_sc = length (Thm.hyp simplify_correct);
pr ("SIMPLIFY_CORRECT NHYP = " ^ Int.toString nhyp_sc ^ "\n");

(* ---- (c) HEADLINE 2: opt_compile_correct ----
   2-line corollary: compile_correct gives
     exec (compile (simplify e)) s = SPush (eval (simplify e)) s,
   then rewrite with simplify_correct. *)
val opt_compile_correct = Tactical.prove(
  Parse.Term [QUOTE "!e s. exec (compile (simplify e)) s = SPush (eval e) s"],
  Rewrite.REWRITE_TAC [compile_correct, simplify_correct]
  ) handle e => (pr ("OPT_COMPILE_CORRECT FAILED: " ^ General.exnMessage e ^ "\n"); raise e);
pr "OK opt_compile_correct\n";

pr "THEOREM opt_compile_correct: ";
pr (Parse.thm_to_string opt_compile_correct);
pr "\n";
val nhyp_oc = length (Thm.hyp opt_compile_correct);
pr ("OPT_COMPILE_CORRECT NHYP = " ^ Int.toString nhyp_oc ^ "\n");
val () = if nhyp_sc = 0 andalso nhyp_oc = 0 then pr "ZERO_HYP_OK\n" else pr "HAS HYPOTHESES!\n";

(* ---- BONUS: EVAL the optimizer folding a MIXED +/* expr ----
   simplify (Plus (Times (Const 3) (Const 4)) (Const 2)) should fold the whole
   tree to a single Const 14 (3*4=12, +2 = 14) — the constant-folder runs and
   the numeral MULTIPLICATION reduces in computeLib (the datatype build repairs
   the numeral-mult compset rules).
   IDIOM: the_compset is a REF -> use computeLib.copy (!computeLib.the_compset);
   add_thms : thm list -> compset -> unit. *)
val () = (
  let
    val cs = computeLib.copy (!computeLib.the_compset);
    val _ = computeLib.add_thms [simplify, mkPlus, mkTimes, eval] cs;
    val res = computeLib.CBV_CONV cs
      (Parse.Term [QUOTE "simplify (Plus (Times (Const 3) (Const 4)) (Const 2))"]);
    val rhs = boolSyntax.rhs (Thm.concl res);
    val expected = Parse.Term [QUOTE "Const 14"];
  in
    pr ("EVAL simplify result: " ^ Parse.thm_to_string res ^ "\n");
    if Term.aconv rhs expected
    then pr "EVAL_OK\n"
    else pr "EVAL DID NOT FOLD TO Const 14\n"
  end
) handle e => pr ("EVAL FAILED: " ^ General.exnMessage e ^ "\n");

pr "ALL_DONE\n";
