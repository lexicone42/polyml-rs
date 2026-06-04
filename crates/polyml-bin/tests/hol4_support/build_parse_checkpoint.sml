(* build_parse_checkpoint.sml — load HOL4's term/type PARSER (src/parse) on
   top of the basis+kernel+Theory checkpoint, then PolyML.export a warm
   "basis + kernel + Theory + parser" image so Parse.Term / Parse.Type can be
   driven directly.
   ---------------------------------------------------------------------------
   BASE CHECKPOINT: /tmp/hol4_theory  (NOT /tmp/hol4_kernel).
   Rationale (measured 2026-06-04, not guessed):
     * src/parse files do `open HolKernel`, which needs Net + Theory + the real
       Overlay (`open Kernel`, top-level QUOTE/ANTIQUOTE/frag).  Those live in
       /tmp/hol4_theory, NOT in /tmp/hol4_kernel.
     * /tmp/hol4_theory already contains, each with a SINGLE identity:
         locn smpp seq optmonad FunctionalRecordUpdate Net Theory HolKernel
         Type Term Thm KernelSig Table HOLPP UTF8 ... (and QUOTE in scope).
       We must NOT reload any of these — reloading mints a duplicate opaque
       identity and triggers the parse_type.sml:306
       "Can't unify ?.locn.locn (*opaque*)" failure that blocked earlier
       attempts.
     * The cross-dir leaves ABSENT from /tmp/hol4_theory that src/parse needs
       are:  errormonad, seqmonad, stmonad  (src/portableML/monads),
       KNametab  (src/prekernel), and  UTF8Set  (src/portableML, used by
       term_tokens.sml).  We load exactly those, fresh, and nothing else from
       outside src/parse.  Their own deps (Portable / seq / Option / Table /
       KernelSig / HOLPP / Inttab) are all present with single identity, so no
       duplication occurs.
   ---------------------------------------------------------------------------
   base_lexer.sml is the ml-lex-GENERATED scanner.  It is CHECKED IN
   (vendor/hol4/src/parse/base_lexer.sml, 6105 lines) and loads cleanly on our
   interpreter — so the historical "mllex infinite-loops / generated-lexer
   wall" does not apply here.  term_tokens.sml has already been rewritten to
   \DDD escapes (byte-identical) so our lexer accepts it.
   ---------------------------------------------------------------------------
   DEFERRED (NOT loaded; not on the Parse.Term/Parse.Type critical path):
     selftest.sml (the ONLY high-byte file in src/parse — would trip the lexer),
     testutils.{sig,sml}, TacticParse.{sig,sml}, ReplCommands.{sig,sml},
     ParseDatatype_dtype.sml + ParseDatatype.{sig,sml} (Datatype surface),
     and Hol_pp.{sig,sml} — Hol_pp.sig declares `type theory = DB.theory` /
     `DB.data` / `DB.selector`, and `structure DB` is the theorem-DB SEARCH
     layer which is NOT in /tmp/hol4_theory (it needs the regexpMatch library,
     unvendored).  No core parse file depends on Hol_pp, so deferring it is safe.
     AncestryData / GrammarDeltas / GrammarAncestry are KEPT (load-bearing for
     Parse: Parse.sml:1085 AncestryData.make, :561/583/682/710/713/802
     GrammarDeltas.record_tmdelta) and load fine on the theory base, where
     Theory / ThyDataSexp / LoadableThyData are present single-identity.

   KEYSTONE FIX (verified 2026-06-04): the parser core was blocked by a
   missing pervasive `Interrupt`.  Real PolyML installs Interrupt/Bind/Match
   into the INITIAL top-level namespace (INITIALISE_.ML:524); basis/General.sml
   re-binds Bind/Match/Overflow/etc. but NOT Interrupt, and our checkpoint
   export/reload drops the compiler-pervasive one — so a bare `Interrupt` is
   UNBOUND on these checkpoints.  HOL4's src/portableML/Portable.sml uses the
   standard `... handle Interrupt => raise Interrupt | _ => NONE` idiom for
   Lib.total / Lib.can / with_exn; with Interrupt unbound those parse as a
   catch-all VARIABLE that re-raises EVERYTHING, so total/can NEVER return
   NONE.  That silently broke term_grammar's min_grammar build
   (Overload.add_overloading -> strip_comb -> total dest_comb re-raised
   "not a comb") and ~22 downstream parse modules.  The fix lives in
   build_kernel_checkpoint.sml (`exception Interrupt = RunCall.Interrupt;`
   before Portable.sml compiles) — so REBUILD the kernel + Theory checkpoints
   before running this script.  Earlier drafts mis-probed this with a freshly
   compiled handler (which sees a correctly-bound Interrupt if one is in scope)
   and wrongly concluded "no bug".  The export below is GATED on the smoke test
   so a broken build is never shipped — inspect STUCKWHY lines for any stall.
   ---------------------------------------------------------------------------
   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_theory \
       crates/polyml-bin/tests/hol4_support/build_parse_checkpoint.sml
   Produces /tmp/hol4_parse.
   Emits: PARSE_PREFIX_DONE, LOADED_OK n/m, STUCK_COUNT n, STUCKERR <path>…,
          smoke-test sentinels (TYPE_OK / TERM_OK / LAMBDA_OK …),
          EXPORTING /tmp/hol4_parse, PARSE_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);

(* ../hol4 relative to cwd = vendor/polyml. Our runtime's OS.Process.getEnv
   returns SOME "" for set vars, so only honor a NON-empty value. *)
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";

(* Robust loader: wrap PolyML.use in a handler so an exception (e.g. a missing
   file's Io, or a compile failure surfacing as an exn) cannot trip the VM's
   "exception packet called as closure -> non-closure value" halt.  Prints
   USED_OK / USE_FAIL per file. *)
fun U f =
    let val path = HOL ^ "/" ^ f
    in (PolyML.use path; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;

(* HOL4 compiles every parse file with Overlay as prelude; `structure PP`
   must be HOLPP for the parse sources to see PP.frag etc. *)
structure PP = HOLPP;

(* type_pp.sml:15 reads `Systeml.OS` (val avoid_unicode = ref (Systeml.OS =
   "winNT")).  The Systeml baked into /tmp/hol4_theory (theory_subsystem.sml)
   only has HOLDIR/release/version/build_log_file/make_log_file — no OS — so
   re-bind a complete Systeml here (transparent; only files compiled after
   this point see it, which is exactly type_pp and friends). *)
structure Systeml = struct
  val HOLDIR = HOL
  val release = "polyml-rs"
  val version = 0
  val build_log_file = ""
  val make_log_file = ""
  val OS = "unix"
end;

pr "\nPARSE_PREFIX_START\n";

(* --- absent cross-dir leaves, loaded FRESH (sig before sml) ---------------
   These are the ONLY files we pull from outside src/parse.  Each one's deps
   are already present (single identity) on /tmp/hol4_theory. *)
val _ = U "src/portableML/monads/errormonad.sig";
val _ = U "src/portableML/monads/errormonad.sml";
val _ = U "src/portableML/monads/seqmonad.sig";   (* needs errormonad + seq  *)
val _ = U "src/portableML/monads/seqmonad.sml";
val _ = U "src/portableML/monads/stmonad.sig";    (* self-contained          *)
val _ = U "src/portableML/monads/stmonad.sml";
val _ = U "src/prekernel/KNametab.sml";           (* Table(...) functor app  *)
val _ = U "src/portableML/UTF8Set.sig";           (* used by term_tokens     *)
val _ = U "src/portableML/UTF8Set.sml";
(* AncestryData.sml needs SymGraph + ImplicitGraph (directed-graph libs).
   SymGraph = Graph(...) (a functor app), Graph needs AList; ImplicitGraph
   needs only HOLset (present).  Load AList -> Graph -> SymGraph, plus
   ImplicitGraph; their other deps (Table/HOLset/HOLPP/Portable) are present
   single-identity on /tmp/hol4_theory. *)
val _ = U "src/portableML/AList.sig";
val _ = U "src/portableML/AList.sml";
val _ = U "src/portableML/Graph.sml";             (* inline GRAPH sig+functor *)
val _ = U "src/portableML/SymGraph.sml";          (* = Graph(string key)      *)
val _ = U "src/portableML/ImplicitGraph.sig";
val _ = U "src/portableML/ImplicitGraph.sml";
pr "PARSE_PREFIX_DONE\n";

(* --- the src/parse closure -----------------------------------------------
   Ordered roughly by the dependency edges extracted from the sources
   (datatypes first, then sigs, then implementations).  The fixpoint loop
   below resolves any residual ordering — a file that fails on pass k because
   a sibling isn't loaded yet is retried on pass k+1.  .sig precedes its .sml.
   Files known not to be on the term/type-parser critical path (selftest,
   testutils, ReplCommands, TacticParse, ParseDatatype) are omitted. *)
val files = [
  (* HOLgrammars + GrammarSpecials FIRST: several *_dtype files do
     `open HOLgrammars` / reference GrammarSpecials, so these must precede
     them.  (Getting this wrong leaves term_grammar_dtype's constructors
     unbound, which cascades into "X already bound in this match" in
     term_grammar.sml and stalls the whole parser core.) *)
  "src/parse/HOLgrammars.sml",
  "src/parse/GrammarSpecials.sig",            "src/parse/GrammarSpecials.sml",
  (* leaf datatypes / small structures *)
  "src/parse/Pretype_dtype.sml",
  "src/parse/term_grammar_dtype.sml",
  "src/parse/parse_term_dtype.sml",
  "src/parse/base_tokens_dtype.sml",
  "src/parse/term_pp_utils_dtype.sml",
  "src/parse/HOLtokens.sig",                  "src/parse/HOLtokens.sml",
  "src/parse/CharSet.sig",                    "src/parse/CharSet.sml",
  "src/parse/MLstring.sig",                   "src/parse/MLstring.sml",
  "src/parse/Literal.sig",                    "src/parse/Literal.sml",
  "src/parse/typecheck_error.sml",
  (* tokenizers + the GENERATED lexer + quote buffer *)
  "src/parse/base_tokens.sig",                "src/parse/base_tokens.sml",
  "src/parse/base_lexer.sml",                 (* ml-lex generated, checked in *)
  "src/parse/qbuf.sig",                       "src/parse/qbuf.sml",
  "src/parse/type_tokens_dtype.sml",
  "src/parse/type_tokens.sig",                "src/parse/type_tokens.sml",
  "src/parse/term_tokens.sig",                "src/parse/term_tokens.sml",
  (* nets used by grammars / overloading *)
  "src/parse/FCNet.sig",                      "src/parse/FCNet.sml",
  "src/parse/TypeNet.sig",                    "src/parse/TypeNet.sml",
  "src/parse/LVTermNet.sig",                  "src/parse/LVTermNet.sml",
  "src/parse/LVTermNetFunctor.sml",
  (* type side: grammar + parser + pretypes *)
  "src/parse/type_grammar_dtype.sml",
  "src/parse/type_grammar.sig",               "src/parse/type_grammar.sml",
  "src/parse/parse_type.sig",                 "src/parse/parse_type.sml",
  "src/parse/Pretype.sig",                    "src/parse/Pretype.sml",
  (* abstract syntax *)
  "src/parse/Absyn_dtype.sml",
  "src/parse/Absyn.sig",                      "src/parse/Absyn.sml",
  (* overloading + precedence + term grammar *)
  "src/parse/Overload.sig",                   "src/parse/Overload.sml",
  "src/parse/PrecAnalysis.sig",               "src/parse/PrecAnalysis.sml",
  "src/parse/term_pp_types.sml",
  "src/parse/Parse_supportENV.sml",
  "src/parse/term_grammar.sig",               "src/parse/term_grammar.sml",
  "src/parse/GrammarDeltas.sig",              "src/parse/GrammarDeltas.sml",
  "src/parse/GrammarAncestry.sig",            "src/parse/GrammarAncestry.sml",
  "src/parse/AncestryData.sig",               "src/parse/AncestryData.sml",
  (* preterms + term parser + parse-support *)
  "src/parse/Preterm_dtype.sml",
  "src/parse/Preterm.sig",                    "src/parse/Preterm.sml",
  "src/parse/Parse_support.sig",              "src/parse/Parse_support.sml",
  "src/parse/parse_term.sig",                 "src/parse/parse_term.sml",
  "src/parse/ProvideUnicode.sig",             "src/parse/ProvideUnicode.sml",
  (* pretty-printing (needed by Parse's signature) *)
  "src/parse/PPBackEnd.sig",                  "src/parse/PPBackEnd.sml",
  "src/parse/term_pp_utils.sig",              "src/parse/term_pp_utils.sml",
  "src/parse/type_pp.sig",                    "src/parse/type_pp.sml",
  "src/parse/term_pp.sig",                    "src/parse/term_pp.sml",
  (* top of the parser stack *)
  "src/parse/TermParse.sig",                  "src/parse/TermParse.sml",
  "src/parse/Parse.sig",                      "src/parse/Parse.sml"
  (* Hol_pp.{sig,sml} DEFERRED: needs structure DB (theorem-DB search layer),
     absent from /tmp/hol4_theory.  Not on the Parse.Term/Parse.Type path. *)
];

(* fixpoint loader: retry each file across passes until no new one loads.
   (Same shape as theory_subsystem.sml's loader.) *)
val errs = ref ([] : (string * string) list);
fun note (f, e) = errs := (f, e) :: (List.filter (fn (g,_) => g <> f) (!errs));
fun tryUse f =
    (PolyML.use (HOL ^ "/" ^ f); true)
    handle e => (note (f, exnMessage e); false);
fun pass (rem, prog) =
  case rem of
      [] => (prog, [])
    | f :: rest =>
        if tryUse f
        then let val (p,l) = pass(rest,true)  in (p, l)     end
        else let val (p,l) = pass(rest,prog) in (p, f::l)  end;
fun loop (rem, n) =
  if n <= 0 then rem
  else let val (_, left) = pass (rem, false)
       in if List.null left then []
          else if List.length left = List.length rem then left  (* no progress *)
          else loop (left, n - 1)
       end;

pr "FIXPOINT_START\n";
val stuck = loop (files, 30);
pr ("\nLOADED_OK " ^ Int.toString (List.length files - List.length stuck)
    ^ "/" ^ Int.toString (List.length files) ^ "\n");
pr ("STUCK_COUNT " ^ Int.toString (List.length stuck) ^ "\n");
List.app (fn f => pr ("STUCKERR " ^ f ^ "\n")) stuck;
(* surface the last recorded error for each stuck file (diagnostic) *)
List.app (fn f =>
             case List.find (fn (g,_) => g = f) (!errs) of
                 SOME (_, e) => pr ("STUCKWHY  " ^ f ^ " :: " ^ e ^ "\n")
               | NONE => ())
         stuck;
pr "PARSE_SUBSYSTEM_DONE\n";

(* ------------------------------------------------------------------------ *)
(* SMOKE TEST — parse a type and terms needing NO theory constants.         *)
(*   Parse.Type [QUOTE ":'a -> 'a"]  -> a function type                     *)
(*   Parse.Term [QUOTE "x:'a"]       -> a variable                          *)
(*   Parse.Term [QUOTE "\\x. x"]     -> a lambda abstraction                *)
(* QUOTE / frag are already in top-level scope via Overlay on the base      *)
(* checkpoint, so no quotation plumbing is needed.                          *)
(* ------------------------------------------------------------------------ *)
pr "SMOKE_START\n";
val smoke_pass = ref true;
fun smoke_fail tag e = (smoke_pass := false;
                        pr ("SMOKE_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
val () =
    (let val ty = Parse.Type [QUOTE ":'a -> 'a"]
     in if Lib.can Type.dom_rng ty
        then pr "TYPE_OK\n"
        else (smoke_pass := false; pr "SMOKE_FAIL type :: not a function type\n")
     end)
    handle e => smoke_fail "Parse.Type" e;
val () =
    (let val tm = Parse.Term [QUOTE "x:'a"]
     in if Term.is_var tm andalso #1 (Term.dest_var tm) = "x"
        then pr "TERM_OK\n"
        else (smoke_pass := false; pr "SMOKE_FAIL term :: not var x\n")
     end)
    handle e => smoke_fail "Parse.Term-var" e;
val () =
    (let val tm = Parse.Term [QUOTE "\\x. x"]
         val (v, body) = Term.dest_abs tm
     in if Term.is_var v andalso Term.aconv v body
        then pr "LAMBDA_OK\n"
        else (smoke_pass := false; pr "SMOKE_FAIL lambda :: body<>bvar\n")
     end)
    handle e => smoke_fail "Parse.Term-lambda" e;
pr (if !smoke_pass then "PARSE_SMOKE_PASS\n" else "PARSE_SMOKE_FAIL\n");
pr "SMOKE_DONE\n";

(* Export ONLY if the parser actually works — never ship a broken image. *)
val () =
    if !smoke_pass then
      (pr "EXPORTING /tmp/hol4_parse\n";
       PolyML.export("/tmp/hol4_parse", PolyML.rootFunction);
       pr "PARSE_CHECKPOINT_DONE\n")
    else pr "PARSE_CHECKPOINT_SKIPPED (smoke failed)\n";
