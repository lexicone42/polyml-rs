(* build_marker_checkpoint.sml — build HOL4's markerTheory (a real *Script.sml
   theory with tactic proofs) on top of the warm REWRITE_TAC checkpoint, and
   export /tmp/hol4_marker.  This is the first theory built on a NON-EMPTY base
   (bool) via the generalized Script->Theory recipe, exercising the new_theory
   export keystone fix (Globals.interactive + the Theory.sml:1178 patch).
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_rewrite (basis+kernel+Theory+parser+bool+tactic+REWRITE_TAC).

   src/marker/markerScript.sml is "Theory marker[bare]" + "Libs HolKernel Parse
   boolLib" and proves ~12 theorems with REWRITE_TAC/STRIP_TAC/AP_TERM_TAC/
   AP_THM_TAC/MATCH_ACCEPT_TAC.  We:
     1. Provide the names markerScript opens via a SYNTHESIZED `structure boolLib`
        (the real boolLib does not load on our checkpoint — grammarDB{bool}=NONE
        + backtick quotations; a minimal synthesized one suffices for marker).
        It re-exports boolTheory/boolSyntax/Drule/Conv/Tactical/Tactic/Thm_cont/
        Rewrite/Abbrev/BoundedRewrites (covers store_thm=Tactical, new_definition
        =boolSyntax, REWRITE_TAC=Rewrite, STRIP_TAC/REPEAT/AP_*_TAC/
        MATCH_ACCEPT_TAC=Tactic/Tactical, CONJ_ASSOC/CONJ_COMM=boolTheory).
     2. Declare the tactic infixes (THEN/ORELSE/...) — HOL4 normally gets these
        from per-file .ui interfaces we don't have.
     3. Load OpenTheoryMap (markerScript's only directly-absent leaf).
     4. Run the Script->Theory recipe: quote-filter -> neutralize export_theory
        -> PolyML.use -> synthesize `structure markerTheory` from the live
        segment (Theory.current_{axioms,definitions,theorems}()).

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_rewrite \
       crates/polyml-bin/tests/hol4_support/build_marker_checkpoint.sml
   Produces /tmp/hol4_marker.  Emits: FILTER_LOADED n/m, MARKER_USED_OK,
   MARKER_THEORY current=marker, MARKERTHEORY_NAMES n, MARKER_SMOKE_PASS|FAIL,
   EXPORTING /tmp/hol4_marker, MARKER_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
structure PP = HOLPP;
val explode = String.explode;
val implode = String.implode;
structure Definition = Theory.Definition;
fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;
(* tactic infixes (markerScript uses THEN and a parenthesized ORELSE). *)
infix THEN THENL THEN1 ORELSE;
(* synthesized boolLib: the names markerScript's "Libs ... boolLib" opens. *)
structure boolLib = struct
  open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite Abbrev BoundedRewrites
end;

pr "\nMARKER_FILTER_START\n";
structure Systeml = struct
  val HOLDIR = HOL  val release = "polyml-rs"  val version = 0
  val build_log_file = ""  val make_log_file = ""  val OS = "unix"
  val canBindStr = true
end;
val filterFiles = [
  "src/portableML/DString.sig",        "src/portableML/DString.sml",
  "src/portableML/DArray.sig",         "src/portableML/DArray.sml",
  "tools/parsing/AttributeSyntax.sig", "tools/parsing/AttributeSyntax.sml",
  "tools/util/SimpleBuffer.sig",       "tools/util/SimpleBuffer.sml",
  "tools/parsing/HOLSourceAST.sig",    "tools/parsing/HOLSourceAST.sml",
  "tools/parsing/HOLSourceParser.sig", "tools/parsing/HOLSourceParser.sml",
  "tools/parsing/HOLSourceExpand.sig", "tools/parsing/HOLSourceExpand.sml",
  "tools/parsing/HOLSourcePrinter.sig","tools/parsing/HOLSourcePrinter.sml",
  "tools/parsing/HOLSource.sig",       "tools/parsing/HOLSource.sml"
];
val nfilt = foldl (fn (f,a) => if U f then a+1 else a) 0 filterFiles;
pr ("FILTER_LOADED " ^ Int.toString nfilt ^ "/" ^ Int.toString (length filterFiles) ^ "\n");

(* markerScript's only directly-absent leaf. *)
val _ = U "src/opentheory/OpenTheoryMap.sig";
val _ = U "src/opentheory/OpenTheoryMap.sml";

(* Register the bool axioms into Theory.replayed_axioms BEFORE switching theory.
   Our synthesized boolTheory keeps each theorem's LIVE tag (with axiom nonces),
   unlike HOL4's disk-loaded DISK_THM theorems (nonces stripped).  So a marker
   theorem proved via e.g. CONJ_COMM inherits a bool-axiom nonce, and
   Theory.uptodate_thm's uptodate_axioms (which only searches the CURRENT
   theory's axioms + replayed_axioms) would reject it as out-of-date.  Registering
   the ancestor (bool) axioms — exactly what replayed_axioms is for — makes the
   nonce resolve.  current=bool here (before new_theory "marker"). *)
val () = app (fn (nm, ax) =>
                 (Theory.register_replayed_axiom ax; pr ("REG_AX " ^ nm ^ "\n"))
                 handle e => pr ("REG_AX_FAIL " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
             (Theory.current_axioms());

(* recipe: filter markerScript, neutralize export_theory, write, use. *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/marker/markerScript.sml");
val (pre, suf) = Substring.position "export_theory" (Substring.full raw);
val neutralized =
    Substring.string pre ^ "current_theory"
    ^ Substring.string (Substring.triml (size "export_theory") suf);
val () = let val os = TextIO.openOut "/tmp/markerScript_filtered.sml"
         in TextIO.output(os, neutralized); TextIO.closeOut os end;
val () = (PolyML.use "/tmp/markerScript_filtered.sml"; pr "MARKER_USED_OK\n")
         handle e => pr ("MARKER_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("MARKER_THEORY current=" ^ Theory.current_theory() ^ "\n");

(* synthesize structure markerTheory from the live segment. *)
val all_named =
    Theory.current_axioms() @ Theory.current_definitions() @ Theory.current_theorems();
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
val () = pr ("MARKERTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () = let val os = TextIO.openOut "/tmp/markerTheory_gen.sml"
         in TextIO.output(os, "structure markerTheory = struct\n");
            app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
                (!btbl);
            TextIO.output(os, "end;\n"); TextIO.closeOut os
         end;
val () = (PolyML.use "/tmp/markerTheory_gen.sml"; pr "MARKERTHEORY_STRUCT_LOADED\n")
         handle e => pr ("MARKERTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* smoke: marker segment + a known theorem/constant. *)
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n") else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "marker-current" (Theory.current_theory() = "marker");
val () = need "stmarker-const" ((ignore (Term.prim_mk_const{Name="stmarker",Thy="marker"}); true) handle _ => false);
val () = need "stmarker_def"   ((ignore markerTheory.stmarker_def; true) handle _ => false);
val () = need "Abbrev_CONG"    ((ignore markerTheory.Abbrev_CONG;  true) handle _ => false);
val () = pr (if !smoke then "MARKER_SMOKE_PASS\n" else "MARKER_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_marker\n";
       PolyML.export("/tmp/hol4_marker", PolyML.rootFunction);
       pr "MARKER_CHECKPOINT_DONE\n")
    else pr "MARKER_CHECKPOINT_SKIPPED\n";
