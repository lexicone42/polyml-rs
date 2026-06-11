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

   The EVAL bonus uses a Plus-ONLY program (2+(3+4)=9): numeral MULTIPLICATION
   does not reduce on this checkpoint (reduceLib/REDUCE/DECIDE leave 3*4 as a
   symbolic NUMERAL(numeral$iZ ..) form — a known degradation, see the
   numsimps notes), while addition reduces fine. The Plus-only demo still fully
   exercises Push + Add + code concatenation, proved as two real 0-hyp theorems
   (the machine RUN agrees with the source EVAL).

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

(* ---- BONUS: prove a concrete compiled program RUNS and agrees with eval ----
   PITFALL: this checkpoint's numeral arithmetic only evaluates ADDITION
   (reduceLib/ARITH/DECIDE compute 2+3=5 but leave 3*4 symbolic — numeral
   multiplication is non-functional in /tmp/hol4_datatype).  So the demo uses
   a Plus-only program, which still fully exercises Push + Add + code
   concatenation on the stack machine:
       exec (compile (Plus (Const 2) (Plus (Const 3) (Const 4)))) SNil
         = SPush 9 SNil       (and eval of the source = 9 too).
   REWRITE with the function defs reduces the structural part to
   SPush (2 + (3 + 4)) SNil; REDUCE_CONV finishes the addition to 9. *)
val () = (
  let
    val concrete = Tactical.prove(
      Parse.Term [QUOTE
        "exec (compile (Plus (Const 2) (Plus (Const 3) (Const 4)))) SNil = SPush 9 SNil"],
      Tactical.THEN (Rewrite.REWRITE_TAC [compile, capp, exec],
                     Tactic.CONV_TAC reduceLib.REDUCE_CONV));
    (* and check the source eval agrees: eval (...) = 9 *)
    val evalThm = Tactical.prove(
      Parse.Term [QUOTE "eval (Plus (Const 2) (Plus (Const 3) (Const 4))) = 9"],
      Tactical.THEN (Rewrite.REWRITE_TAC [eval],
                     Tactic.CONV_TAC reduceLib.REDUCE_CONV));
  in
    pr ("EVAL THEOREM (machine run): " ^ Parse.thm_to_string concrete ^ "\n");
    pr ("EVAL THEOREM (source eval): " ^ Parse.thm_to_string evalThm ^ "\n");
    if length (Thm.hyp concrete) = 0 andalso length (Thm.hyp evalThm) = 0
    then pr "EVAL_OK\n"
    else pr "EVAL HAS HYPS\n"
  end
) handle e => pr ("EVAL FAILED: " ^ General.exnMessage e ^ "\n");
