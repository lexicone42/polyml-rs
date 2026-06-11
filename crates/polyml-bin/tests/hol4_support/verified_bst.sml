(* ============================================================================
   VERIFIED BINARY SEARCH TREE over num keys, in HOL4 on the polyml-rs interpreter.
   Checkpoint: /tmp/hol4_datatype  (Datatype, Define, arithmeticTheory, simpLib,
   metisLib present; NO listTheory).  Self-contained driver.

   Data-structure verification with an INVARIANT (distinct from the algorithmic
   /compiler proofs): a binary search tree (tree = Leaf | Node tree num tree)
   with insert/member, the ordering predicates all_lt/all_gt, and the BST
   invariant `bst`. Two headline theorems, both ZERO-hypothesis:

     member_insert : |- !t x y. member x (insert y t) <=> (x = y) \/ member x t
                     (insert adds EXACTLY y to the key set — membership is correct)
     insert_bst    : |- !t x. bst t ==> bst (insert x t)
                     (insert PRESERVES the BST ordering invariant)

   The membership/bound lemmas (member_insert, all_lt_insert, all_gt_insert) all
   close with the same idiom: byInd, REWRITE_TAC[insert_def], REPEAT
   COND_CASES_TAC, ASM_REWRITE_TAC[def], then METIS over the small trichotomy set
   [LESS_LESS_CASES, LESS_ANTISYM, LESS_TRANS, NOT_LESS].

   THE ONE PITFALL — insert_bst: STRIP_TAC strips the antecedent `bst (Node ..)`
   into the assumptions as a SINGLE FOLDED term (it does not expand definitions),
   so the all_lt/bst subfacts are not separately available and plain ASM_REWRITE
   cannot discharge them. FIX: FULL_SIMP_TAC (bool_ss ++ ARITH_ss) with
   [bst_def, all_lt_def, all_gt_def, all_lt_insert, all_gt_insert] expands the
   folded hypothesis AND pushes the bound predicates through insert; the residual
   `bst (insert x sub)` then follows from the IH by plain propositional MP
   (METIS_TAC[] with an EMPTY lemma list — feeding the iff-shaped push-through
   lemmas to METIS causes a search explosion / unbounded GC retention).

   Engineered by a 3-seat ultracode fleet (wf_6bef35bc-140); all three seats
   verified independently, all with the EVAL demo.
   ============================================================================ *)
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL ORELSE;
open boolLib;
pr "BST_START\n";

(* === datatype: tree = Leaf | Node tree num tree (backticks NOT parsed) === *)
val _ = Datatype.Datatype [QUOTE "tree = Leaf | Node tree num tree"];
val SOME tyi = TypeBase.fetch (Type.mk_thy_type {Thy=Theory.current_theory(),Tyop="tree",Args=[]});
val tree_ind = TypeBasePure.induction_of tyi;
(* reusable structural-induction tactic *)
fun byInd tac = Tactical.THEN (Tactic.HO_MATCH_MP_TAC tree_ind,
    Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));

(* === function definitions (parenthesise every conjunct whose RHS has ops) === *)
val insert_def = TotalDefn.Define [QUOTE
  "(insert x Leaf = Node Leaf x Leaf) /\\ (insert x (Node l v r) = (if x < v then Node (insert x l) v r else if v < x then Node l v (insert x r) else Node l v r))"];
val member_def = TotalDefn.Define [QUOTE
  "(member x Leaf = F) /\\ (member x (Node l v r) = (if x < v then member x l else if v < x then member x r else T))"];
val all_lt_def = TotalDefn.Define [QUOTE
  "(all_lt b Leaf = T) /\\ (all_lt b (Node l v r) = ((v < b) /\\ all_lt b l /\\ all_lt b r))"];
val all_gt_def = TotalDefn.Define [QUOTE
  "(all_gt b Leaf = T) /\\ (all_gt b (Node l v r) = ((b < v) /\\ all_gt b l /\\ all_gt b r))"];
val bst_def = TotalDefn.Define [QUOTE
  "(bst Leaf = T) /\\ (bst (Node l v r) = (all_lt v l /\\ all_gt v r /\\ bst l /\\ bst r))"];
pr "OK defs\n";

(* trichotomy / antisymmetry bookkeeping facts (all present on this image) *)
val ORDER = [arithmeticTheory.LESS_LESS_CASES, arithmeticTheory.LESS_ANTISYM,
             arithmeticTheory.LESS_TRANS, arithmeticTheory.NOT_LESS];
val ss = simpLib.++(boolSimps.bool_ss, numSimps.ARITH_ss);

fun chkhyp name th =
  let val h = Thm.hyp th
  in pr ("OK " ^ name ^ (if null h then " [0 hyps]\n"
                          else " [HYPS=" ^ Int.toString (length h) ^ " !!]\n")) end;

(* === HELPER LEMMAS (prove BEFORE insert_bst, then feed them in) === *)
(* every key in (insert x t) is < b  iff  x < b and every key in t is < b *)
val all_lt_insert =
  Tactical.prove(Parse.Term [QUOTE "!t b x. all_lt b (insert x t) <=> (x < b) /\\ all_lt b t"],
    byInd (Tactical.THEN (Rewrite.REWRITE_TAC[insert_def],
      Tactical.THEN (Tactical.REPEAT Tactic.COND_CASES_TAC,
        Tactical.THEN (Rewrite.ASM_REWRITE_TAC[all_lt_def],
          metisLib.METIS_TAC ORDER)))));
chkhyp "all_lt_insert" all_lt_insert;

val all_gt_insert =
  Tactical.prove(Parse.Term [QUOTE "!t b x. all_gt b (insert x t) <=> (b < x) /\\ all_gt b t"],
    byInd (Tactical.THEN (Rewrite.REWRITE_TAC[insert_def],
      Tactical.THEN (Tactical.REPEAT Tactic.COND_CASES_TAC,
        Tactical.THEN (Rewrite.ASM_REWRITE_TAC[all_gt_def],
          metisLib.METIS_TAC ORDER)))));
chkhyp "all_gt_insert" all_gt_insert;

(* === HEADLINE 1 — membership is correct: insert adds EXACTLY y === *)
val member_insert =
  Tactical.prove(Parse.Term [QUOTE "!t x y. member x (insert y t) <=> (x = y) \\/ member x t"],
    byInd (Tactical.THEN (Rewrite.REWRITE_TAC[insert_def],
      Tactical.THEN (Tactical.REPEAT Tactic.COND_CASES_TAC,
        Tactical.THEN (Rewrite.ASM_REWRITE_TAC[member_def],
          metisLib.METIS_TAC ORDER)))));
chkhyp "member_insert" member_insert;

(* === HEADLINE 2 — insert PRESERVES the BST invariant ===
   FULL_SIMP_TAC expands the folded `bst (Node ..)` hypothesis into its conjuncts
   and pushes the bound predicates through `insert` with the two helper lemmas;
   the sole residual `bst (insert x sub)` is then discharged from the inductive
   hypothesis by plain propositional MP (METIS_TAC[] — empty lemma list, no search
   explosion). *)
val insert_bst =
  Tactical.prove(Parse.Term [QUOTE "!t x. bst t ==> bst (insert x t)"],
    byInd (Tactical.THEN (Rewrite.REWRITE_TAC[insert_def, bst_def],
      Tactical.THEN (Tactical.REPEAT Tactic.COND_CASES_TAC,
        Tactical.THEN (simpLib.FULL_SIMP_TAC ss [bst_def, all_lt_def, all_gt_def, all_lt_insert, all_gt_insert],
          metisLib.METIS_TAC [])))));
chkhyp "insert_bst" insert_bst;

pr "THEOREMS_DONE\n";

(* === BONUS: concrete evaluation via computeLib === *)
val evalDemo =
  let
    val cs = computeLib.copy (!computeLib.the_compset);
    val _ = computeLib.add_thms [insert_def, member_def] cs;
    fun ev s = computeLib.CBV_CONV cs (Parse.Term [QUOTE s]);
    (* member 3 (insert 5 (insert 3 (insert 8 Leaf))) should be T (3 was inserted) *)
    val t1 = ev "member 3 (insert 5 (insert 3 (insert 8 Leaf)))";
    (* member 4 (...) should be F (4 was never inserted) *)
    val t2 = ev "member 4 (insert 5 (insert 3 (insert 8 Leaf)))";
    val r1 = boolSyntax.rhs (Thm.concl t1);
    val r2 = boolSyntax.rhs (Thm.concl t2);
    val ok1 = Term.term_eq r1 boolSyntax.T;
    val ok2 = Term.term_eq r2 boolSyntax.F;
  in
    pr ("eval member3 -> " ^ term_to_string r1 ^ "\n");
    pr ("eval member4 -> " ^ term_to_string r2 ^ "\n");
    if ok1 andalso ok2 then (pr "EVAL_OK\n"; true)
    else (pr "EVAL_MISMATCH\n"; false)
  end handle e => (pr ("eval EXN: " ^ General.exnMessage e ^ "\n"); false);

pr "BST_DONE\n";

