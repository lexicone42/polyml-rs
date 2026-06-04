(* build_bool_checkpoint.sml — build the HOL4 `bool` theory on top of the warm
   parser checkpoint and export /tmp/hol4_bool (basis+kernel+Theory+parser+bool).
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_parse  (basis + kernel + Theory + the full term/type parser).

   boolScript.sml is written in HOL4's modern script syntax — `Theory bool[bare]`,
   `Definition`/`Theorem`, and 700+ unicode `“…”` term quotations — so it cannot
   be compiled directly.  HOL4 normally preprocesses scripts with the
   quote-filter.  The GOOD NEWS (measured 2026-06-04): the modern filter
   (tools/parsing/HOLSource{AST,Parser,Expand,Printer} + DString/DArray/
   AttributeSyntax/SimpleBuffer) is HAND-WRITTEN SML (NOT ml-lex/yacc generated)
   and loads + runs on our interpreter.  We load it, run it on the REAL
   boolScript.sml, and PolyML.use the resulting plain-ASCII SML.  The filter's
   HOLSourcePrinter.encodeStr emits in-body unicode as \DDD escapes, so the
   output is pure ASCII and never trips our string lexer's >=0x80 rejection.

   Two wrinkles handled here:
   1. HOLSourceExpand.sml:149 reads `Systeml.canBindStr`, absent from the baked
      Systeml stub — so we re-bind a complete Systeml (with canBindStr) first.
   2. `Theory.export_theory ()` does heavy filesystem finalize (OS.FileSys.getDir,
      path ops, file writes) and raises on our runtime, which trips the
      exception-unwinding halt.  We don't need the on-disk .dat/.sml — only the
      in-memory bool SEGMENT — so we NEUTRALIZE the export_theory call (rewrite
      it to a no-op Theory.current_theory call) in the filtered source.

   The generated `<thy>Theory.sml` (which would bind each saved theorem to an SML
   val inside `structure boolTheory`) is also produced by export_theory.  Since
   we skip that, we SYNTHESIZE `structure boolTheory` ourselves from the live
   segment via Theory.current_{axioms,definitions,theorems}() — exactly the names
   the src/1 tactic layer opens.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_parse \
       crates/polyml-bin/tests/hol4_support/build_bool_checkpoint.sml
   Produces /tmp/hol4_bool.  Emits: FILTER_LOADED n/m, NEUTRALIZED_BYTES n,
   BOOLSCRIPT_USED_OK, BOOLTHEORY_NAMES n, BOOLTHEORY_STRUCT_LOADED,
   BOOL_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_bool, BOOL_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;
structure PP = HOLPP;
(* (1) complete Systeml so HOLSourceExpand.sml:149 (canBindStr) compiles. *)
structure Systeml = struct
  val HOLDIR = HOL  val release = "polyml-rs"  val version = 0
  val build_log_file = ""  val make_log_file = ""  val OS = "unix"
  val canBindStr = true
end;

pr "\nBOOL_FILTER_START\n";
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
val nok = foldl (fn (f,a) => if U f then a+1 else a) 0 filterFiles;
val () = pr ("FILTER_LOADED " ^ Int.toString nok ^ "/"
             ^ Int.toString (length filterFiles) ^ "\n");

(* (2) filter the real boolScript, neutralize export_theory, write plain SML. *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/bool/boolScript.sml");
val (pre, suf) = Substring.position "export_theory" (Substring.full raw);
val neutralized =
    Substring.string pre ^ "current_theory"
    ^ Substring.string (Substring.triml (size "export_theory") suf);
val () = let val os = TextIO.openOut "/tmp/boolScript_filtered.sml"
         in TextIO.output(os, neutralized); TextIO.closeOut os end;
val () = pr ("NEUTRALIZED_BYTES " ^ Int.toString (size neutralized) ^ "\n");

(* runtime targets boolScript names bare/qualified that aren't top-level here. *)
structure Definition = Theory.Definition;
structure Unicode = Parse.Unicode;
val _ = U "src/bool/TexTokenMap.sig"; val _ = U "src/bool/TexTokenMap.sml";
val _ = U "src/bool/boolpp.sig";      val _ = U "src/bool/boolpp.sml";

val () = (PolyML.use "/tmp/boolScript_filtered.sml"; pr "BOOLSCRIPT_USED_OK\n")
         handle e => pr ("BOOLSCRIPT_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("CURRENT_THEORY " ^ Theory.current_theory() ^ "\n");

(* (3) synthesize `structure boolTheory` from the live segment. *)
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
val () = pr ("BOOLTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () = let val os = TextIO.openOut "/tmp/boolTheory_gen.sml"
         in TextIO.output(os, "structure boolTheory = struct\n");
            app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
                (!btbl);
            TextIO.output(os, "end;\n"); TextIO.closeOut os
         end;
val () = (PolyML.use "/tmp/boolTheory_gen.sml"; pr "BOOLTHEORY_STRUCT_LOADED\n")
         handle e => pr ("BOOLTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* smoke: the bool segment + the theorems the tactic layer reads at init. *)
val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "bool-current"   (Theory.current_theory() = "bool");
val () = need "conj-const"     ((ignore (Term.prim_mk_const{Name="/\\",Thy="bool"}); true) handle _ => false);
val () = need "EQ_CLAUSES"     ((ignore boolTheory.EQ_CLAUSES;  true) handle _ => false);
val () = need "IMP_CLAUSES"    ((ignore boolTheory.IMP_CLAUSES; true) handle _ => false);
val () = need "NOT_CLAUSES"    ((ignore boolTheory.NOT_CLAUSES; true) handle _ => false);
val () = need "OR_CLAUSES"     ((ignore boolTheory.OR_CLAUSES;  true) handle _ => false);
val () = need "TRUTH"          ((ignore boolTheory.TRUTH;       true) handle _ => false);
val () = pr (if !smoke then "BOOL_SMOKE_PASS\n" else "BOOL_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_bool\n";
       PolyML.export("/tmp/hol4_bool", PolyML.rootFunction);
       pr "BOOL_CHECKPOINT_DONE\n")
    else pr "BOOL_CHECKPOINT_SKIPPED (smoke failed)\n";
