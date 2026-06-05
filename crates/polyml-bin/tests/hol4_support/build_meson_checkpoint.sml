(* build_meson_checkpoint.sml — assemble HOL4's first-order automated prover
   (mesonLib / MESON_TAC) on top of the warm simp checkpoint, export /tmp/hol4_meson.
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_simp (…+combin+simpLib). We base on simp, NOT combin/taut,
   because Canon_Port and mesonLib `open liteLib` + `Ho_Rewrite`, which were
   loaded by the simp build and persist in /tmp/hol4_simp. /tmp/hol4_taut has
   tautLib but (built on combin) lacks those leaves.

   mesonLib also `open`s tautLib, which is NOT on simp — so this driver first
   REPLAYS the taut layer on simp (satTheory + HolSat closure + tautLib, exactly
   as build_taut_checkpoint.sml does on combin), then loads the 6-file meson
   closure (Canon_Port, jrhTactics, mesonLib).

   THREE keystones (all proven elsewhere in this dir):
   1. simp's synthesized boolLib lacks `save_thm_at` (satScript's Theorem-save
      needs it). We SHADOW it with the widened boolLib from build_combin (which
      hand-rolls save_thm_at via Theory.gen_save_thm) BEFORE building satTheory.
   2. tautLib fixes its grammar via `grammarDB{bool}` = NONE on our synthesized
      boolTheory → patched to the global Parse grammar (build_taut recipe).
   3. Canon_Port wants `grammarDB{combin}` and mesonLib wants `grammarDB{bool}`,
      both NONE here → same global-Parse patch.

   SAT note: TAUT_PROVE runs via HOL4's pure-SML DPLL solver (no external
   minisat); needs OS.FileSys.tmpName/remove (IO subcodes 67/64, in rts.rs).

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_simp \
       crates/polyml-bin/tests/hol4_support/build_meson_checkpoint.sml
   Produces /tmp/hol4_meson. Emits: FILTER_LOADED, SATTHEORY_NAMES 24,
   HOLSAT_LOADED 13/13, TAUTLIB_LOADED, CANON_PORT_OK, JRHTACTICS_OK,
   MESONLIB_OK, MESON <tag>: …, MESON_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_meson,
   MESON_CHECKPOINT_DONE. *)

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
infix THEN THENL THEN1 ORELSE;

(* (0) widened boolLib (from build_combin_checkpoint.sml) — supplies save_thm_at,
   which simp's synthesized boolLib omits. Shadows simp's boolLib for the rest
   of the load. *)
structure boolLib =
struct
  open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite
       Abbrev BoundedRewrites Parse
  val EQ_IMP_RULE     = Thm.EQ_IMP_RULE
  val CONJ            = Thm.CONJ
  val add_ML_dependency = Theory.add_ML_dependency
  fun do_known_attrs name th attrs =
      List.app
        (fn (k,vs) =>
            ThmAttribute.store_at_attribute
              {thm = th, name = name, attrname = k, args = vs})
        attrs
  fun handle_reserved call R = ()
  fun save_thm_attrs loc (attrblock:ThmAttribute.attrblock, th) =
      let val {thmname=n,attrs,unknown,reserved} = attrblock
      in handle_reserved "save_thm_attrs" reserved;
         Theory.gen_save_thm{name=n,private=false,thm=th,loc=loc};
         do_known_attrs n th attrs;
         th
      end
  fun save_thm_at loc (n0,th) =
      save_thm_attrs loc (ThmAttribute.extract_attributes n0, th)
  val save_thm = save_thm_at Theory.Unknown
  fun store_thm_at loc (n0,t,tac) =
      let val attrblock = ThmAttribute.extract_attributes n0
          val th = Tactical.prove(t,tac)
      in save_thm_attrs loc (attrblock,th) end
  val store_thm = store_thm_at Theory.Unknown
  val new_definition_at = boolSyntax.new_definition_at
  val new_definition = boolSyntax.new_definition
  val new_infixl_definition = boolSyntax.new_infixl_definition
  val new_infixr_definition = boolSyntax.new_infixr_definition
end;

(* (1) complete Systeml so the quote-filter compiles (canBindStr). *)
structure Systeml = struct
  val HOLDIR = HOL  val release = "polyml-rs"  val version = 0
  val build_log_file = ""  val make_log_file = ""  val OS = "unix"
  val canBindStr = true
  fun protect s = s
  val system_ps = OS.Process.system
end;

pr "\nMESON_FILTER_START\n";
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
val () = (PolyML.use "/tmp/satScript_filtered.sml"; pr "SATSCRIPT_USED_OK\n")
         handle e => pr ("SATSCRIPT_USE_FAIL :: " ^ exnMessage e ^ "\n");

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

(* (4) computeLib + minisatParse stubs (dead external-solver path). *)
structure computeLib = struct
  val EVAL_CONV : Term.term -> Thm.thm =
      fn _ => raise Fail "computeLib.EVAL_CONV stub (SAT/cex path unused)"
end;
structure minisatParse = struct
  fun replayProof _ _ _ _ _ _ _ _ = (NONE : Thm.thm option)
end;

(* (5) load the HolSat closure, then tautLib (grammarDB{bool} patched). *)
pr "HOLSAT_LOAD_START\n";
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
];
val hcount = foldl (fn (f,a) => if useHOL f then a+1 else a) 0 holsatFiles;
val () = pr ("HOLSAT_LOADED " ^ Int.toString hcount ^ "/"
             ^ Int.toString (length holsatFiles) ^ "\n");

fun rs (s, f, r) =
    let val (p,sf) = Substring.position f (Substring.full s)
    in if Substring.isEmpty sf then s
       else Substring.string p ^ r ^ Substring.string (Substring.triml (size f) sf) end;
fun patchFile (src, outp, edits) =
    let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/" ^ src))
        val patched = foldl (fn ((f,r),acc) => rs(acc,f,r)) raw edits
        val os = TextIO.openOut outp
    in TextIO.output(os, patched); TextIO.closeOut os; outp end;
(* Like patchFile, but also runs the quote-filter (HOLSource.inputFile) so HOL
   term quotations `` ``…`` `` become [QUOTE "…"]. The grammar patches are applied
   to the raw text first (those lines are plain SML, untouched by the filter). *)
fun filterFileHOL (src, outp, edits) =
    let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/" ^ src))
        val patched = foldl (fn ((f,r),acc) => rs(acc,f,r)) raw edits
        val tmp = outp ^ ".pre"
        val () = let val os = TextIO.openOut tmp
                 in TextIO.output(os, patched); TextIO.closeOut os end
        val filtered = HOLSource.inputFile {quietOpen=false, print=fn _ => ()} tmp
        val os = TextIO.openOut outp
    in TextIO.output(os, filtered); TextIO.closeOut os; outp end;

val tautPatched = patchFile ("src/taut/tautLib.sml", "/tmp/tautLib_patched.sml",
  [("val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}",
    "val bool_grammars = ()"),
   ("val (Type,Term) = parse_from_grammars bool_grammars",
    "val (Type,Term) = (Parse.Type, Parse.Term)")]);
val _ = useHOL "src/taut/tautLib.sig";
val () = (PolyML.use tautPatched; pr "TAUTLIB_LOADED\n")
         handle e => pr ("TAUTLIB_FAIL :: " ^ exnMessage e ^ "\n");
(* tautLib smoke gate *)
val () = (let val th = tautLib.TAUT_PROVE (Parse.Term [QUOTE "p \\/ ~p"])
          in pr ("TAUT_SMOKE: " ^ Parse.thm_to_string th ^ "\n") end)
         handle e => pr ("TAUT_SMOKE_FAIL :: " ^ exnMessage e ^ "\n");

(* (6) the meson closure: Canon_Port (patched), jrhTactics, mesonLib (patched). *)
pr "MESON_LOAD_START\n";
val canonF = filterFileHOL ("src/meson/src/Canon_Port.sml", "/tmp/Canon_Port_filtered.sml",
  [("val SOME combin_grammars = grammarDB {thyname=\"combin\"}",
    "val combin_grammars = Parse.current_grammars()"),
   ("val _ = Parse.temp_set_grammars combin_grammars", "val _ = ()")]);
val _ = useHOL "src/meson/src/Canon_Port.sig";
val () = (PolyML.use canonF; pr "CANON_PORT_OK\n")
         handle e => pr ("CANON_PORT_FAIL :: " ^ exnMessage e ^ "\n");

val _ = useHOL "src/meson/src/jrhTactics.sig";
val () = (PolyML.use (HOL ^ "/src/meson/src/jrhTactics.sml"); pr "JRHTACTICS_OK\n")
         handle e => pr ("JRHTACTICS_FAIL :: " ^ exnMessage e ^ "\n");

val mesonF = filterFileHOL ("src/meson/src/mesonLib.sml", "/tmp/mesonLib_filtered.sml",
  [("val SOME bool_grammars = Parse.grammarDB {thyname=\"bool\"}",
    "val bool_grammars = Parse.current_grammars()"),
   ("val _ = Parse.temp_set_grammars bool_grammars", "val _ = ()")]);
val _ = useHOL "src/meson/src/mesonLib.sig";
val () = (PolyML.use mesonF; pr "MESONLIB_OK\n")
         handle e => pr ("MESONLIB_FAIL :: " ^ exnMessage e ^ "\n");

(* (7) MESON proofs — genuinely first-order goals (need instantiation/Skolem). *)
val () = (mesonLib.chatting := 0) handle _ => ();
val smoke = ref true;
fun meson tag s =
    let val g = Parse.Term [QUOTE s]
        val th = Tactical.prove(g, mesonLib.MESON_TAC [])
    in pr ("MESON " ^ tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
       if null (Thm.hyp th) andalso Term.aconv (Thm.concl th) g then ()
       else smoke := false
    end handle e => (smoke := false; pr ("MESON_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
val () = meson "SYLL"    "(!x. P x ==> Q x) /\\ P a ==> Q a";
val () = meson "DRINKER" "?x. D x ==> !y. D y";
val () = meson "CHAIN"   "(!x. P x ==> Q x) /\\ (!x. Q x ==> R x) /\\ P a ==> R a";
val () = pr (if !smoke then "MESON_SMOKE_PASS\n" else "MESON_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_meson\n";
       PolyML.export("/tmp/hol4_meson", PolyML.rootFunction);
       pr "MESON_CHECKPOINT_DONE\n")
    else pr "MESON_CHECKPOINT_SKIPPED (smoke failed)\n";
