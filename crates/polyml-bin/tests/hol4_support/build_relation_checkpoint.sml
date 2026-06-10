(* build_relation_checkpoint.sml — Stage 2 of the Datatype roadmap: build the
   REAL relationTheory on /tmp/hol4_prim_rec and export /tmp/hol4_relation.

   relationScript.sml (2618 lines: TC/RTC, wellfoundedness, fixpoints) needs:
     * IndDefLib (the `Inductive RTC:` block) — loaded for REAL here (Stage 8's
       package, banked early): InductiveDefinition.sml carries backtick
       quotations -> quote-filtered; IndDefRules/IndDefLib load raw.
     * BasicProvers — SHIMMED (real one needs TypeBase/AncestryData):
       srw_ss=ref bool_ss, SRW_TAC=strip+FULL_SIMP, PROVE_TAC=ASM_MESON_TAC,
       `by`=Q.SUBGOAL_THEN, Cases_on/Induct_on raise (splice those proofs).
     * QLib — empty shim (the script only uses Q. qualified names).
     * Theorem attributes [simp] (no-op registered; BasicProvers territory);
       [mono]/[rule_induction] are registered by IndDefLib itself if it loads.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 400000000000 \
       /tmp/hol4_prim_rec crates/polyml-bin/tests/hol4_support/build_relation_checkpoint.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val FRAGDIR = HOL ^ "/../../crates/polyml-bin/tests/hol4_support";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
infix THEN THENL THEN1 ORELSE;
infix 8 by;

pr "\nRELATION_BUILD_START\n";
val () = Globals.interactive := true;

val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax; pr ("REG_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_AX_NOTE " ^ nm ^ " (already)\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];

(* no-op [simp] attribute (BasicProvers registers the real one). *)
val () =
    app (fn a =>
       (if ThmAttribute.is_attribute a then pr ("ATTR_ALREADY " ^ a ^ "\n")
        else (ThmAttribute.register_attribute
                (a, {storedf = (fn _ => ()), localf = (fn _ => ())});
              pr ("ATTR_REGISTERED " ^ a ^ "\n")))
       handle e => pr ("ATTR_FAIL " ^ a ^ " :: " ^ exnMessage e ^ "\n"))
    ["simp"];

(* ---------------------------------------------------------------------------
   BasicProvers SHIM + QLib. Semantic stand-ins over machinery we DO have:
   mesonLib, simpLib/bool_ss, Q. (Real BasicProvers needs TypeBase+Ancestry.)
   --------------------------------------------------------------------------- *)
structure BasicProvers = struct
  val srw_ss_ref = ref boolSimps.bool_ss
  fun srw_ss () = !srw_ss_ref
  fun augment_srw_ss frags =
      srw_ss_ref := List.foldl (fn (f, ss) => simpLib.++ (ss, f)) (!srw_ss_ref) frags
  fun export_rewrites (_ : string list) = ()
  fun SRW_TAC frags thl =
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
        simpLib.FULL_SIMP_TAC
          (List.foldl (fn (f, ss) => simpLib.++ (ss, f)) (srw_ss ()) frags) thl)
  fun PROVE_TAC thl = mesonLib.ASM_MESON_TAC thl
  val prove_tac = PROVE_TAC
  fun PROVE thl tm = Tactical.prove (tm, PROVE_TAC thl)
  fun Cases_on (_ : Term.term Abbrev.quotation) : Abbrev.tactic =
      raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Cases_on" "needs TypeBase"
  fun Induct_on (_ : Term.term Abbrev.quotation) : Abbrev.tactic =
      raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Induct_on" "needs TypeBase"
end;
structure QLib = struct end;

(* `q by tac`: prove subgoal q with tac (must close it), strip-assume into goal. *)
fun (q by tac) =
    Tactical.THEN1 (Q.SUBGOAL_THEN q Tactic.STRIP_ASSUME_TAC,
                    Tactical.THEN (tac, Tactical.NO_TAC));

(* ---------------------------------------------------------------------------
   IndDefLib for real. InductiveDefinition.sml carries backticks -> filter.
   --------------------------------------------------------------------------- *)
fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;
val parts_ok = ref true;
fun usePart tag f =
    (PolyML.use f; pr ("USED_OK   " ^ tag ^ "\n"))
    handle e => (parts_ok := false;
                 pr ("USE_FAIL  " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
fun replaceAll (s, old, new) =
    let val (pre, suf) = Substring.position old (Substring.full s)
    in if Substring.size suf = 0 then s
       else Substring.string pre ^ new
            ^ replaceAll (Substring.string (Substring.triml (size old) suf), old, new)
    end;
fun useFiltered tag patches src =
    let val txt0 = HOLSource.inputFile {quietOpen = false, print = fn _ => ()} src
        val txt = List.foldl (fn ((old, new), t) => replaceAll (t, old, new)) txt0 patches
        val tmp = "/tmp/filtered_" ^ tag ^ ".sml"
    in writeFile (tmp, txt); usePart tag tmp end;
(* grammarDB{bool} = NONE on our synthesized boolTheory -> global Parse
   grammars (the established build_taut/meson/metis patch). *)
(* NB the quote-filter tokenizes with spaces: `{ thyname = "bool" }`. *)
val grammarPatch =
    [("val SOME bool_grammars = grammarDB { thyname = \"bool\" }",
      "val bool_grammars = Parse.current_grammars()")];

(* widen boolLib: IndDef wants boolLib.def_suffix (ref "_def" in the real one;
   our synthesized boolLib chain lacks it). Also fix save_thm_at: the
   prim_rec-era shim passed raw `name[attr]` through — strip the attribute
   block (attrs like [simp] are no-ops on this chain). *)
structure boolLib = struct
  open boolLib
  val def_suffix = ref "_def"
  fun save_thm_at _ (n, th) =
      Theory.save_thm (hd (String.fields (fn c => c = #"[") n), th)
end;

val () = usePart "InductiveDefinition.sig" (HOL ^ "/src/IndDef/InductiveDefinition.sig");
val () = useFiltered "InductiveDefinition" grammarPatch (HOL ^ "/src/IndDef/InductiveDefinition.sml");
val () = usePart "IndDefRules.sig" (HOL ^ "/src/IndDef/IndDefRules.sig");
val () = usePart "IndDefRules" (HOL ^ "/src/IndDef/IndDefRules.sml");
(* widen the DB stub BEFORE ThmSetData compiles against it: serve lookups in
   the CURRENT segment for real (IndDefLib re-fetches RTC_strongind right
   after saving it); log + defer to the old stub otherwise. *)
structure DB = struct
  open DB
  fun fetch thy nm =
      if thy = Theory.current_theory () orelse thy = "-" then
        (case List.find (fn (n, _) => n = nm)
                        (Theory.current_theorems () @ Theory.current_definitions ()
                         @ Theory.current_axioms ()) of
             SOME (_, th) => th
           | NONE => (pr ("DB_FETCH_MISS " ^ thy ^ " . " ^ nm ^ "\n");
                      DB.fetch thy nm))
      else (pr ("DB_FETCH_REQ " ^ thy ^ " . " ^ nm ^ "\n"); DB.fetch thy nm)
end;

val () = usePart "ThmSetData.sig" (HOL ^ "/src/1/ThmSetData.sig");
val () = usePart "ThmSetData" (HOL ^ "/src/1/ThmSetData.sml");
val () = usePart "IndDefLib.sig" (HOL ^ "/src/IndDef/IndDefLib.sig");
val () = usePart "IndDefLib"   (HOL ^ "/src/IndDef/IndDefLib.sml");
(* the Inductive-block expansion calls CompilerSpecific.quietbind (a tiny
   PolyML.compiler-based eval, from Holmake's poly support). *)
val () = usePart "CompilerSpecific" (HOL ^ "/tools-poly/Holmake/CompilerSpecific.ML");

(* instrument the DB stub: log what fetch is asked for, then defer to old. *)
structure DB = struct
  open DB
  fun fetch thy nm =
      (pr ("DB_FETCH_REQ " ^ thy ^ " . " ^ nm ^ "\n"); DB.fetch thy nm)
end;

(* ---------------------------------------------------------------------------
   relationScript, filtered; export_theory neutralized.
   --------------------------------------------------------------------------- *)
(* SATISFY_ss (existential-witness simpset fragment), used by two SRW_TACs.
   Closure: Sequence (lazy sequences) + Unify (both small, src/simp leaves). *)
val () = usePart "Sequence.sig" (HOL ^ "/src/simp/src/Sequence.sig");
val () = usePart "Sequence" (HOL ^ "/src/simp/src/Sequence.sml");
val () = usePart "Unify.sig" (HOL ^ "/src/simp/src/Unify.sig");
val () = useFiltered "Unify" [] (HOL ^ "/src/simp/src/Unify.sml");
val () = usePart "Satisfy.sig" (HOL ^ "/src/simp/src/Satisfy.sig");
val () = useFiltered "Satisfy" [] (HOL ^ "/src/simp/src/Satisfy.sml");
val () = usePart "SatisfySimps.sig" (HOL ^ "/src/simp/src/SatisfySimps.sig");
val () = usePart "SatisfySimps" (HOL ^ "/src/simp/src/SatisfySimps.sml");

(* now that IndDefLib is live, widen the BasicProvers shim with a lightweight
   rule-induction Induct_on (lookup in the REAL rule_induction_map, try
   HO_MATCH_MP_TAC on each registered theorem) and a bool-only Cases_on.
   Both parse their quotation in goal context. *)
structure BasicProvers = struct
  open BasicProvers
  (* SRW_TAC closer pass: real SRW uses assumptions as rewrites at the end
     (e.g. goal `R x y \/ R y x` with asm `R x y` must close). *)
  fun SRW_TAC frags thl =
      Tactical.THEN (Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
        simpLib.FULL_SIMP_TAC
          (List.foldl (fn (f, ss) => simpLib.++ (ss, f)) (srw_ss ()) frags) thl),
        Tactical.TRY (Tactical.THEN (Rewrite.ONCE_ASM_REWRITE_TAC [], Tactical.THEN (Rewrite.REWRITE_TAC [], Tactical.NO_TAC))))
  (* lowercase aliases the script uses (real defs from BasicProvers). *)
  fun RW_TAC ss thl =
      Tactical.THEN (Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
        simpLib.FULL_SIMP_TAC ss thl),
        Tactical.TRY (Tactical.THEN (Rewrite.ONCE_ASM_REWRITE_TAC [], Tactical.THEN (Rewrite.REWRITE_TAC [], Tactical.NO_TAC))))
  val rw_tac = RW_TAC
  fun simp thl = simpLib.ASM_SIMP_TAC (srw_ss ()) thl
  fun parse_ctxt q (asl, w) =
      Parse.parse_in_context (Term.free_varsl (w :: asl)) q
  fun Induct_on q (g as (asl, w)) =
      let val tm = parse_ctxt q g
          val (c, _) = boolSyntax.strip_comb tm
          val {Thy, Name, ...} = Term.dest_thy_const c
          val ths = Option.getOpt
                      (KNametab.lookup (IndDefLib.rule_induction_map ())
                                       {Thy = Thy, Name = Name}, [])
          fun try [] = raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Induct_on"
                             ("no applicable rule-induction for " ^ Name)
            | try (th :: rest) =
                Tactic.HO_MATCH_MP_TAC th g handle Feedback.HOL_ERR _ => try rest
      in try ths end
  fun Cases_on q (g as (asl, w)) =
      let val tm = parse_ctxt q g
      in if Term.type_of tm = Type.bool then Tactic.ASM_CASES_TAC tm g
         else raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Cases_on"
                    "non-bool Cases_on needs TypeBase"
      end
end;

fun splitAt (s, anchor) =
    let val (pre, suf) = Substring.position anchor (Substring.full s)
    in if Substring.size suf = 0
       then (pr ("ANCHOR_MISSING [" ^ anchor ^ "]\n"); (s, ""))
       else (Substring.string pre, Substring.string suf)
    end;

val raw = HOLSource.inputFile {quietOpen = false, print = fn _ => ()}
              (HOL ^ "/src/relation/relationScript.sml");
val neutralized =
    let val (pre, suf) = Substring.position "export_theory" (Substring.full raw)
    in if Substring.size suf = 0 then raw
       else Substring.string pre ^ "current_theory"
            ^ Substring.string (Substring.triml (size "export_theory") suf)
    end;
(* split around EQC_INDUCTION (its PAT_X_ASSUM proof fails here; spliced),
   and SKIP the rest of the EQC niceties (EQC_MOVES_IN.., deep real-SRW
   coupling; not on the arithmetic path) to resume at the WF block. *)
val (rel1, rest) = splitAt (neutralized, "val EQC_INDUCTION");
val (_, rest)    = splitAt (rest, "val EQC_REFL");
val (rel2, rest) = splitAt (rest, "val EQC_MOVES_IN");
val (_, rel3)    = splitAt (rest, "val WF_DEF");
val () = writeFile ("/tmp/relation_part1.sml", rel1);
val () = writeFile ("/tmp/relation_part2.sml", rel2);
val () = writeFile ("/tmp/relation_part3.sml", rel3);
val () = usePart "relation_part1(..EXTEND_RTC)" "/tmp/relation_part1.sml";
val () = usePart "fragR1(EQC_INDUCTION)" (FRAGDIR ^ "/relation_frag_eqc_induction.sml");
val () = usePart "relation_part2(EQC_REFL..EQC_TRANS)" "/tmp/relation_part2.sml";
val () = pr "SKIPPED EQC_MOVES_IN..pre-WF (EQC tail; not on the arithmetic path)\n";
(* part3 = WF core; part4 = inv_image onward (WF_PULL skipped: Cases_on-proof
   coupling; niche). Later failures inside a part abort that part only — the
   decls before the failure are already saved. *)
val (rel3a, rest3) = splitAt (rel3, "val WF_PULL");
val (_, rel3b)     = splitAt (rest3, "val inv_image_def");
val () = writeFile ("/tmp/relation_part3.sml", rel3a);
val () = writeFile ("/tmp/relation_part4.sml", rel3b);
val () = usePart "relation_part3(WF_DEF..WF_NOT_REFL)" "/tmp/relation_part3.sml";
val () = pr "SKIPPED WF_PULL (Cases_on proof; niche)\n";
val () = usePart "relation_part4(inv_image..)" "/tmp/relation_part4.sml";

val () = pr ("RELATION current=" ^ Theory.current_theory () ^ "\n");

(* ---------------------------------------------------------------------------
   synthesize structure relationTheory; smoke; export.
   --------------------------------------------------------------------------- *)
val all_named =
    Theory.current_axioms () @ Theory.current_definitions () @
    Theory.current_theorems ();
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub (s, 0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val seen = ref ([] : string list);
val btbl = ref ([] : (string * Thm.thm) list);
val () = app (fn (n, th) =>
                 if validName n andalso not (List.exists (fn m => m = n) (!seen))
                 then (seen := n :: !seen; btbl := (n, th) :: !btbl) else ())
             all_named;
fun bt n = #2 (valOf (List.find (fn (m, _) => m = n) (!btbl)));
val () = pr ("RELATIONTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () =
    let val os = TextIO.openOut "/tmp/relationTheory_gen.sml"
    in TextIO.output (os, "structure relationTheory = struct\n");
       app (fn (n, _) =>
               TextIO.output (os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
           (!btbl);
       TextIO.output (os, "end;\n"); TextIO.closeOut os
    end;
val () = (PolyML.use "/tmp/relationTheory_gen.sml"; pr "RELATIONTHEORY_STRUCT_LOADED\n")
         handle e => pr ("RELATIONTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* export gates on the CRITICAL names (the TC/RTC + WF fragment the arithmetic
   stages need), not on every part loading — the EQC tail / stragglers are
   skipped by design (logged above) and tracked for a full-fidelity pass. *)
val () = if !parts_ok then () else pr "NOTE some parts failed/skipped (see USE_FAIL/SKIPPED)\n";
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "relation-current" (Theory.current_theory () = "relation");
val () = need "TC_DEF"        ((ignore (bt "TC_DEF");        true) handle _ => false);
val () = need "RTC_INDUCT"    ((ignore (bt "RTC_INDUCT");    true) handle _ => false);
val () = need "RTC_RULES"     ((ignore (bt "RTC_RULES");     true) handle _ => false);
val () = need "RTC_CASES_TC"  ((ignore (bt "RTC_CASES_TC");  true) handle _ => false);
val () = need "TC_CASES2"     ((ignore (bt "TC_CASES2");     true) handle _ => false);
val () = need "WF_DEF"        ((ignore (bt "WF_DEF");        true) handle _ => false);
val () = need "WF_INDUCTION_THM" ((ignore (bt "WF_INDUCTION_THM"); true) handle _ => false);
val () = need "transitive_def" ((ignore (bt "transitive_def"); true) handle _ => false);
val () = pr (if !smoke then "RELATION_SMOKE_PASS\n" else "RELATION_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_relation\n";
       PolyML.export ("/tmp/hol4_relation", PolyML.rootFunction);
       pr "RELATION_CHECKPOINT_DONE\n")
    else pr "RELATION_CHECKPOINT_SKIPPED\n";
