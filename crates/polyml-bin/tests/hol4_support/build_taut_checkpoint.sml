(* build_taut_checkpoint.sml — assemble HOL4's SAT layer (HolSatLib) and the
   propositional tautology prover (tautLib) on top of the warm combin
   checkpoint, and export /tmp/hol4_taut.
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_combin (basis+kernel+Theory+parser+bool+tactic+REWRITE_TAC+
   marker+combin, synthesized boolLib, empty `structure computeLib` stub).

   THE BREAKTHROUGH (scouted 2026-06-05): HOL4 does NOT need an external minisat
   binary on our runtime. minisatProve.invoke_solver gates the external solver on
   `access(getSolverExe solver,[A_EXEC])` (minisatProve.sml:60); the binary is
   absent (only C++ source is vendored), our fs_access returns false for it, so
   the call falls straight through to the pure-SML `DPLL_TAUT` prover
   (minisatProve.sml:72-76, dpll.sml) — genuine kernel inference, no shell-out.
   The only RTS gap was OS.FileSys.tmpName (IO subcode 67): dimacsTools writes a
   DIMACS temp file via tmpName BEFORE the DPLL fallback fires, and the missing
   subcode faulted. That is now implemented in rts.rs (commit 3930551), so the
   real HolSat machinery loads and DPLL proves the load-time tautologies.

   satTheory (a pile of propositional tautologies the HolSat modules `open`) is
   built from satScript.sml the same Script->Theory way as bool/marker/combin:
   satScript is `Theory sat[bare]` and proves everything with TT_TAUT_PROVE
   (BOOL_CASES_TAC + REWRITE_TAC []) — pure bool, no SAT, no computeLib. We run
   it through the quote-filter, neutralize export_theory, and synthesize
   `structure satTheory` from the live segment (exactly the bool recipe).

   computeLib: satTools.sml:119 references computeLib.EVAL_CONV in its SAT/
   countermodel (cex) branch only — never on the UNSAT/proving path — but the
   module must still type-check, so we shadow the empty stub with one exposing a
   single EVAL_CONV : conv that raises if ever reached.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_combin \
       crates/polyml-bin/tests/hol4_support/build_taut_checkpoint.sml
   Produces /tmp/hol4_taut. Emits: FILTER_LOADED n/m, SATSCRIPT_USED_OK,
   SATTHEORY_NAMES n, HOLSAT_LOADED n/m, TAUTLIB_LOADED, TAUT_RESULT ...,
   TAUT_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_taut, TAUT_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val nok = ref 0; val nf = ref 0;
fun useHOL f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); nok := !nok+1; true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); nf := !nf+1; false)
    end;
structure PP = HOLPP;
structure Definition = Theory.Definition;

(* (1) complete Systeml so the quote-filter compiles (canBindStr). *)
structure Systeml = struct
  val HOLDIR = HOL  val release = "polyml-rs"  val version = 0
  val build_log_file = ""  val make_log_file = ""  val OS = "unix"
  val canBindStr = true
  fun protect s = s                     (* shell-quote; never exec'd here *)
  val system_ps = OS.Process.system     (* never reached: DPLL path, no binary *)
end;

pr "\nTAUT_FILTER_START\n";
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
val fcount = foldl (fn (f,a) => if useHOL f then a+1 else a) 0 filterFiles;
val () = pr ("FILTER_LOADED " ^ Int.toString fcount ^ "/"
             ^ Int.toString (length filterFiles) ^ "\n");

(* (2) build satTheory from satScript via the quote-filter (neutralize export). *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/HolSat/satScript.sml");
val (pre, suf) = Substring.position "export_theory" (Substring.full raw);
val neutralized =
    Substring.string pre ^ "current_theory"
    ^ Substring.string (Substring.triml (size "export_theory") suf);
val () = let val os = TextIO.openOut "/tmp/satScript_filtered.sml"
         in TextIO.output(os, neutralized); TextIO.closeOut os end;
val () = pr ("NEUTRALIZED_BYTES " ^ Int.toString (size neutralized) ^ "\n");
val () = (PolyML.use "/tmp/satScript_filtered.sml"; pr "SATSCRIPT_USED_OK\n")
         handle e => pr ("SATSCRIPT_USE_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("CURRENT_THEORY " ^ Theory.current_theory() ^ "\n");

(* (3) synthesize `structure satTheory` from the live segment. *)
val all_named =
    Theory.current_axioms() @ Theory.current_definitions() @ Theory.current_theorems();
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub(s,0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val seen = ref ([] : string list);
val stbl = ref ([] : (string * Thm.thm) list);
val () = app (fn (n,th) =>
                 if validName n andalso not (List.exists (fn m => m = n) (!seen))
                 then (seen := n :: !seen; stbl := (n,th) :: !stbl) else ())
             all_named;
fun st n = #2 (valOf (List.find (fn (m,_) => m = n) (!stbl)));
val () = pr ("SATTHEORY_NAMES " ^ Int.toString (length (!stbl)) ^ "\n");
val () = let val os = TextIO.openOut "/tmp/satTheory_gen.sml"
         in TextIO.output(os, "structure satTheory = struct\n");
            app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = st \"" ^ n ^ "\";\n"))
                (!stbl);
            TextIO.output(os, "end;\n"); TextIO.closeOut os
         end;
val () = (PolyML.use "/tmp/satTheory_gen.sml"; pr "SATTHEORY_STRUCT_LOADED\n")
         handle e => pr ("SATTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* (4) computeLib stub with EVAL_CONV (UNSAT path never calls it). *)
structure computeLib = struct
  val EVAL_CONV : Term.term -> Thm.thm =
      fn _ => raise Fail "computeLib.EVAL_CONV stub (SAT/cex path unused)"
end;

(* (4b) minisatParse stub. The real minisatParse/minisatResolve parse the
   EXTERNAL minisat binary proof-trace — a path we never take (no binary →
   access(solverExe,[A_EXEC]) is false → minisatProve takes the DPLL_TAUT
   branch). minisatProve only references `replayProof` from it (and only on
   the dead external branch), so a NONE-returning stub type-checks and makes
   the genuine intent explicit. (The real module also has a Word/LargeWord
   mismatch in sat_getint on our runtime — irrelevant on the DPLL path.) *)
structure minisatParse = struct
  fun replayProof _ _ _ _ _ _ _ _ = (NONE : Thm.thm option)
end;

(* (5) load the HolSat closure in dependency order, then tautLib. *)
pr "HOLSAT_LOAD_START\n";
val nok0 = !nok; val nf0 = !nf;
(* minisatParse + minisatResolve omitted: stubbed above (dead external path). *)
val holsatFiles = [
  "src/HolSat/SatSolvers.sml",
  "src/HolSat/satConfig.sig",   "src/HolSat/satConfig.sml",
  "src/HolSat/satCommonTools.sml",
  "src/HolSat/def_cnf.sig",     "src/HolSat/def_cnf.sml",
  "src/HolSat/dimacsTools.sml",
  "src/HolSat/satTools.sml",
  "src/HolSat/dpll.sml",
  "src/HolSat/minisatProve.sig","src/HolSat/minisatProve.sml",
  "src/HolSat/HolSatLib.sig",   "src/HolSat/HolSatLib.sml"
  (* tautLib loaded separately below — needs a grammarDB{bool} patch. *)
];
val hcount = foldl (fn (f,a) => if useHOL f then a+1 else a) 0 holsatFiles;
val () = pr ("HOLSAT_LOADED " ^ Int.toString hcount ^ "/"
             ^ Int.toString (length holsatFiles) ^ "\n");

(* tautLib.sml fixes its grammar via `Option.valOf $ grammarDB{thyname="bool"}`,
   which is NONE on our synthesized boolTheory — patch it to the global Parse
   grammar (the same two-line fix used for Prim_rec / simpLib). *)
val () =
  let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/src/taut/tautLib.sml"))
      fun rs (s, f, r) =
          let val (pre,suf) = Substring.position f (Substring.full s)
          in if Substring.isEmpty suf then s
             else Substring.string pre ^ r ^ Substring.string (Substring.triml (size f) suf) end
      val p1 = rs(raw, "val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}",
                       "val bool_grammars = ()")
      val p2 = rs(p1, "val (Type,Term) = parse_from_grammars bool_grammars",
                      "val (Type,Term) = (Parse.Type, Parse.Term)")
      val os = TextIO.openOut "/tmp/tautLib_patched.sml"
  in TextIO.output(os, p2); TextIO.closeOut os end;
val _ = useHOL "src/taut/tautLib.sig";
val () = (PolyML.use "/tmp/tautLib_patched.sml"; pr "TAUTLIB_LOADED\n")
         handle e => pr ("TAUTLIB_FAIL :: " ^ exnMessage e ^ "\n");

(* (6) prove a tautology — exercises the real DPLL path. *)
val smoke = ref true;
fun tryTaut tag s =
    let val tm = Parse.Term [QUOTE s]
        val th = tautLib.TAUT_PROVE tm
    in pr ("TAUT_RESULT " ^ tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
       if null (Thm.hyp th) then () else smoke := false
    end handle e => (smoke := false; pr ("TAUT_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
val () = tryTaut "EXCLUDED_MIDDLE" "p \\/ ~p";
val () = tryTaut "DEMORGAN"        "~(p /\\ q) <=> ~p \\/ ~q";
val () = tryTaut "CURRY"           "(p /\\ q ==> r) <=> (p ==> q ==> r)";
val () = pr (if !smoke then "TAUT_SMOKE_PASS\n" else "TAUT_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_taut\n";
       PolyML.export("/tmp/hol4_taut", PolyML.rootFunction);
       pr "TAUT_CHECKPOINT_DONE\n")
    else pr "TAUT_CHECKPOINT_SKIPPED (smoke failed)\n";
