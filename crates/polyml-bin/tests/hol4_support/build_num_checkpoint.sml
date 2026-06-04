(* build_num_checkpoint.sml — build HOL4's numTheory on the warm combin
   checkpoint (/tmp/hol4_combin) and export /tmp/hol4_num.

   numScript.sml = "Theory num[bare]" + "Ancestors bool" + "Libs HolKernel
   Parse boolLib".  It bootstraps the natural numbers from boolTheory.INFINITY_AX:
   defines SUC_REP/ZERO_REP on :ind, carves out the :num subtype via
   new_type_definition, defines 0 and SUC, and proves NOT_SUC, INV_SUC, and
   — the keystone — INDUCTION:  |- !P. P 0 /\ (!n. P n ==> P(SUC n)) ==> !n. P n.
   ZERO heavy automation: no SIMP_TAC/Define/Datatype/TypeBase.  Every primitive
   it needs is live on /tmp/hol4_combin (probed).

   Recipe (clone of build_marker/build_combin):
     * synthesize structure boolLib (numScript opens it);
     * register bool ancestor axioms via register_replayed_axiom (KEYSTONE);
     * quote-filter numScript, neutralize export_theory -> current_theory,
       PolyML.use;
     * synthesize structure numTheory from the live segment;
     * smoke (INDUCTION present, SUC const, current=num); export.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_combin \
       crates/polyml-bin/tests/hol4_support/build_num_checkpoint.sml          *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
structure PP = HOLPP;

fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;

(* tactic infixes numScript uses (THEN, THENL). *)
infix THEN THENL THEN1 ORELSE;

pr "\nNUM_BUILD_START\n";

(* ---------------------------------------------------------------------------
   synthesized boolLib — the names numScript's "Libs ... boolLib" opens.
   Opens the kernel Thm + Definition so bare new_specification/new_definition/
   new_type_definition/CONJUNCT1/CONJUNCT2/GENL resolve; Drule/Conv/Tactic/
   Tactical/Thm_cont/Rewrite supply the proof combinators; Parse the quotes.
   --------------------------------------------------------------------------- *)
structure boolLib =
struct
  open boolTheory boolSyntax Thm Definition Drule Conv Tactical Tactic
       Thm_cont Rewrite Abbrev BoundedRewrites Parse
end;

(* ---------------------------------------------------------------------------
   KEYSTONE: register the bool ancestor axioms before new_theory.  Our
   synthesized boolTheory keeps each theorem's LIVE axiom-nonce tag; without
   registering bool's axioms, uptodate_thm rejects any num theorem that
   inherits a bool-axiom nonce.  current=combin here, but current_axioms()
   while a descendant of bool still reaches bool's; register them explicitly.
   --------------------------------------------------------------------------- *)
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax;
             pr ("REG_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_AX_FAIL " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];

(* ---------------------------------------------------------------------------
   Script->Theory recipe: filter numScript, neutralize export_theory, use.
   --------------------------------------------------------------------------- *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/num/theories/numScript.sml");
val (pre, suf) = Substring.position "export_theory" (Substring.full raw);
val neutralized =
    Substring.string pre ^ "current_theory"
    ^ Substring.string (Substring.triml (size "export_theory") suf);
val () = let val os = TextIO.openOut "/tmp/numScript_filtered.sml"
         in TextIO.output(os, neutralized); TextIO.closeOut os end;
val () = (PolyML.use "/tmp/numScript_filtered.sml"; pr "NUM_USED_OK\n")
         handle e => pr ("NUM_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("NUM_THEORY current=" ^ Theory.current_theory() ^ "\n");

(* ---------------------------------------------------------------------------
   synthesize structure numTheory from the live segment.
   --------------------------------------------------------------------------- *)
val all_named =
    Theory.current_axioms() @ Theory.current_definitions() @
    Theory.current_theorems();
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub(s,0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val seen = ref ([] : string list);
val btbl = ref ([] : (string * Thm.thm) list);
val () = app (fn (n,th) =>
                 if validName n andalso not (List.exists (fn m => m = n) (!seen))
                 then (seen := n :: !seen; btbl := (n,th) :: !btbl) else ())
             all_named;
fun bt n = #2 (valOf (List.find (fn (m,_) => m = n) (!btbl)));
val () = pr ("NUMTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () = let val os = TextIO.openOut "/tmp/numTheory_gen.sml"
         in TextIO.output(os, "structure numTheory = struct\n");
            app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
                (!btbl);
            TextIO.output(os, "end;\n"); TextIO.closeOut os
         end;
val () = (PolyML.use "/tmp/numTheory_gen.sml"; pr "NUMTHEORY_STRUCT_LOADED\n")
         handle e => pr ("NUMTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------------------------------------------------------------------------
   smoke then export.
   --------------------------------------------------------------------------- *)
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "num-current" (Theory.current_theory() = "num");
val () = need "SUC-const"
              ((ignore (Term.prim_mk_const{Name="SUC",Thy="num"}); true)
               handle _ => false);
val () = need "0-const"
              ((ignore (Term.prim_mk_const{Name="0",Thy="num"}); true)
               handle _ => false);
val () = need "INDUCTION" ((ignore numTheory.INDUCTION; true) handle _ => false);
val () = need "NOT_SUC"   ((ignore numTheory.NOT_SUC;   true) handle _ => false);
val () = need "INV_SUC"   ((ignore numTheory.INV_SUC;   true) handle _ => false);
val () = (pr ("INDUCTION = " ^ Parse.thm_to_string numTheory.INDUCTION ^ "\n"))
         handle e => pr ("INDUCTION_PRINT_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr (if !smoke then "NUM_SMOKE_PASS\n" else "NUM_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_num\n";
       PolyML.export("/tmp/hol4_num", PolyML.rootFunction);
       pr "NUM_CHECKPOINT_DONE\n")
    else pr "NUM_CHECKPOINT_SKIPPED\n";
