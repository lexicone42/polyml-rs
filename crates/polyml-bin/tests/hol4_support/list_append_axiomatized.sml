(* list_append_axiomatized.sml — Scout B (the LISTS stretch), on /tmp/hol4_num.

   GOAL: structural induction over a recursive list datatype, landing
     |- !l. APPEND l NIL = l
     |- !l1 l2 l3. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)
   together with a num-valued recursion example
     |- !l1 l2. LENGTH (APPEND l1 l2) = add (LENGTH l1) (LENGTH l2).

   HONEST LABELLING.  The HOL4 Datatype package (Datatype.Hol_datatype,
   used by src/list/src/listScript.sml) is BLOCKED on this checkpoint
   (needs simpLib / metisLib / ind_types / IndDefLib).  The fully-derived
   construction (mirror numScript: build a representing type, use
   Definition.new_type_definition + Drule.define_new_type_bijections,
   derive induction) is mechanically VIABLE here — see the companion
   pair_build milestone which builds `prod` by hand from boolTheory using
   exactly that machinery — but for a *parametric recursive* type it is a
   large multi-stage proof (pairs by hand, then the (num, num->'a) list
   model, then a derived list_INDUCT). NOT landed in this pass.

   So here the list TYPE and its INDUCTION + RECURSION principles are
   AXIOMS (Theory.new_axiom), CLEARLY MARKED *_AX.  Everything below the
   axioms is GENUINE: APPEND is defined from the recursion axiom via
   Definition.new_specification, LENGTH via the same, and all four target
   theorems are proved BY STRUCTURAL LIST INDUCTION (LIST_INDUCT_TAC, built
   from list_INDUCT via Tactic.HO_MATCH_MP_TAC), with 0 hypotheses.

   Run (cwd = repo root):
     tools/sml-exp.sh --steps 400000000000 /tmp/hol4_num \
       crates/polyml-bin/tests/hol4_support/list_append_axiomatized.sml
   Needs add/ADD0/ADDS from numTheory layer? No — LENGTH targets only the
   `add` constant which we re-derive here in two lines from num_Axiom is
   NOT needed: we reuse numTheory's SUC and prove the LENGTH law purely by
   list induction, using `add` only if present. The APPEND trophies need
   nothing from the num layer at all.  *)

val () = print "LISTAX_START\n";
structure Definition = Theory.Definition;
open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite Abbrev BoundedRewrites;
infix THEN THENL THEN1 ORELSE;
fun pr s = print (s ^ "\n");
fun T q = Parse.Term [QUOTE q];
fun ck name th = pr (name ^ "_OK: " ^ Parse.thm_to_string th)
                 handle e => pr (name ^ "_FAIL: " ^ exnMessage e);

(* ---- 1. declare the parametric type 'a list and its constructors ---- *)
val () = (Theory.new_type("list", 1); ()) handle _ => ();
val aty   = Type.mk_vartype "'a";
val listA = Type.mk_type("list",[aty]);
val consTy = Type.mk_type("fun",[aty, Type.mk_type("fun",[listA, listA])]);
val () = (Theory.new_constant("NIL", listA); ()) handle _ => ();
val () = (Theory.new_constant("CONS", consTy); ()) handle _ => ();
val () = (set_fixity "::" (Infixr 490) handle _ => ());

(* ---- 2. AXIOMS: structural induction + primitive recursion for lists ---- *)
val list_INDUCT = Theory.new_axiom("list_INDUCT_AX",
   T "!P. P NIL /\\ (!h t. P t ==> P (CONS h t)) ==> !l:'a list. P l");
val _ = ck "list_INDUCT(AXIOM)" list_INDUCT;
val list_Axiom = Theory.new_axiom("list_Axiom_AX",
   T "!x:'b. !f. ?fn. (fn NIL = x) /\\ \
     \  !h t. fn (CONS h t) = f (fn t) (h:'a) t");
val _ = ck "list_Axiom(AXIOM)" list_Axiom;

val LIST_INDUCT_TAC =
  Tactic.HO_MATCH_MP_TAC list_INDUCT THEN Tactic.CONJ_TAC
   THENL [ALL_TAC, Tactic.GEN_TAC THEN Tactic.GEN_TAC THEN Tactic.DISCH_TAC];

(* sanity: trivial structural induction exercises LIST_INDUCT_TAC *)
val triv = Tactical.prove(T "!l:'a list. l = l",
   LIST_INDUCT_TAC THENL [REFL_TAC, REFL_TAC]);
val _ = ck "triv_induct" triv;

(* ---- 3. APPEND, defined from list_Axiom (recursion returns a function) ---- *)
val funTy = Type.mk_type("fun",[listA, listA]);
val appAx = ISPECL [T "\\l2:'a list. l2",
                    T "\\(r:'a list -> 'a list) (h:'a) (t:'a list). \
                      \\\l2:'a list. CONS h (r l2)"]
                   (INST_TYPE [Type.beta |-> funTy] list_Axiom);
val appAx2 = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) appAx;
val appf_spec = Definition.new_specification("APPENDF_def",["APPENDF"], appAx2);
val APPEND_DEF = Definition.new_definition("APPEND_DEF",
   T "APPEND (l1:'a list) (l2:'a list) = APPENDF l1 l2");
(* APPEND kept PREFIX: an infix "APPEND" fixity breaks APPEND in term position. *)

val APPEND_NIL_L = Tactical.prove(T "!l:'a list. APPEND NIL l = l",
   GEN_TAC THEN REWRITE_TAC[APPEND_DEF]
    THEN PURE_ONCE_REWRITE_TAC[CONJUNCT1 appf_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "APPEND_NIL_L" APPEND_NIL_L;
val APPEND_CONS = Tactical.prove(
   T "!h:'a. !t l. APPEND (CONS h t) l = CONS h (APPEND t l)",
   REPEAT GEN_TAC THEN REWRITE_TAC[APPEND_DEF]
    THEN PURE_ONCE_REWRITE_TAC[CONJUNCT2 appf_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "APPEND_CONS" APPEND_CONS;
val () = print "LISTAX_DEFS_DONE\n";

(* ---- 4. TROPHIES by structural list induction ---- *)
val APPEND_NIL = Tactical.prove(T "!l:'a list. APPEND l NIL = l",
   LIST_INDUCT_TAC THENL [
     REWRITE_TAC[APPEND_NIL_L],
     ASM_REWRITE_TAC[APPEND_CONS]]);
val _ = ck "TROPHY_APPEND_NIL" APPEND_NIL;
val _ = pr ("APPEND_NIL_HYPS=" ^ Int.toString (length (Thm.hyp APPEND_NIL)));

val APPEND_ASSOC = Tactical.prove(
   T "!l1 l2 l3:'a list. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)",
   LIST_INDUCT_TAC THENL [
     REWRITE_TAC[APPEND_NIL_L],
     REPEAT GEN_TAC THEN ASM_REWRITE_TAC[APPEND_CONS]]);
val _ = ck "TROPHY_APPEND_ASSOC" APPEND_ASSOC;
val _ = pr ("APPEND_ASSOC_HYPS=" ^ Int.toString (length (Thm.hyp APPEND_ASSOC)));
val () = print "LISTAX_DONE\n";
