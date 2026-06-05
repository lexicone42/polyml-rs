(* build_metis_checkpoint.sml — WORK IN PROGRESS (does NOT yet produce a working
   /tmp/hol4_metis). Assembles HOL4's resolution prover (metisLib / METIS_TAC,
   Joe Hurd's "mlib") on top of the warm meson checkpoint.
   ===========================================================================
   STATUS (2026-06-05): the hard, novel part is DONE — the full 33-module mlib*
   prover core loads 33/33 (after the EXTINSTR realToInt/floatToInt rounding-mode
   interpreter fix, commit e4800cf, which mlib's load-time Random->floor needs;
   and after loading portableML Intset/Intmap). The HOL glue Canon, matchTools,
   folMapping, refuteLib, Unwind, pureSimps, BoolExtractShared all load, and
   normalFormsTheory builds via the Script->Theory recipe.

   BLOCKED on the FULL bool_ss: normalForms' load-time proofs use
   `SIMP_TAC boolSimps.bool_ss`, and boolSimps' SSFRAG construction reaches
   markerLib.Cong — but the simp checkpoint baked a STUBBED markerLib (the real
   one needs proofManagerLib, hence the stub). A top-level markerLib shadow can't
   override the simpLib code already compiled against the stub. So finishing METIS
   needs the simp layer REBUILT with a real markerLib (build proofManagerLib, or
   stub only proofManagerLib and load the real markerLib). That is a dedicated
   bool_ss sub-project; this file is the foundation for it. The COND_BOOL_CLAUSES,
   markerLib.{TIDY_ABBREV_CONV,Cong}, DB.fetch, and grammarDB patches below are all
   correct and reusable once the base has a real markerLib.
   ===========================================================================
   BASE: /tmp/hol4_meson (…+simp+taut+mesonLib). METIS is the strongest HOL4
   first-order prover — ordered resolution + paramodulation (equality), where
   MESON is weak. Closure = the 33-module mlib* core (pure SML) + HOL glue
   (Canon, matchTools, folMapping, normalForms[+Theory], folTools, metisTools,
   metisLib).

   Keystones (all proven in build_meson_checkpoint.sml / build_taut):
   - shadow simp's boolLib with the widened one (save_thm_at) for the theory builds;
   - replay the taut layer (satTheory + HolSat + tautLib) so Canon/normalForms,
     which open tautLib, load;
   - build normalFormsTheory via the satScript Script->Theory recipe;
   - route quotation-carrying .sml (Canon, normalForms, folTools) through the
     HOLSource quote-filter; patch grammarDB{...} -> global Parse.
   - Systeml stub gains `val ML_SYSNAME = "poly"` (mlibPortable reads it at load).

   Interpreter prerequisite: EXTINSTR realToInt/floatToInt must consume the
   rounding-mode byte (commit e4800cf) — mlibUseful calls Random->floor at load.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_meson \
       crates/polyml-bin/tests/hol4_support/build_metis_checkpoint.sml
   Produces /tmp/hol4_metis. Emits: FILTER_LOADED, MLIB_LOADED n/33,
   SATTHEORY_NAMES, NORMALFORMS_NAMES, GLUE markers, METIS <tag>: …,
   METIS_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_metis, METIS_CHECKPOINT_DONE. *)

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

(* (0) widened boolLib (save_thm_at) — for the satTheory/normalFormsTheory builds. *)
structure boolLib =
struct
  open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite
       Abbrev BoundedRewrites Parse
  val EQ_IMP_RULE     = Thm.EQ_IMP_RULE
  val CONJ            = Thm.CONJ
  val add_ML_dependency = Theory.add_ML_dependency
  (* COND_BOOL_CLAUSES is a boolLib-level derived theorem (src/1/boolLib.sml:39),
     not a boolTheory one, so our synthesized boolTheory lacks it. boolSimps opens
     boolLib and needs it; re-derive it here with the upstream proof. *)
  val COND_BOOL_CLAUSES = Tactical.prove(
    Parse.Term [QUOTE ("(!b e. (if b then T else e) = (b \\/ e)) /\\ "
                       ^ "(!b t. (if b then t else T) = (b ==> t)) /\\ "
                       ^ "(!b e. (if b then F else e) = (~b /\\ e)) /\\ "
                       ^ "(!b t. (if b then t else F) = (b /\\ t))")],
    Tactical.REPEAT Tactic.CONJ_TAC
      THEN Tactical.REPEAT Tactic.GEN_TAC
      THEN Tactic.COND_CASES_TAC
      THEN Rewrite.ASM_REWRITE_TAC
             [boolTheory.OR_CLAUSES, boolTheory.AND_CLAUSES,
              boolTheory.NOT_CLAUSES, boolTheory.IMP_CLAUSES])
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

(* (1) Systeml stub (+ ML_SYSNAME for mlibPortable). *)
structure Systeml = struct
  val HOLDIR = HOL  val release = "polyml-rs"  val version = 0
  val build_log_file = ""  val make_log_file = ""  val OS = "unix"
  val canBindStr = true
  val ML_SYSNAME = "poly"
  fun protect s = s
  val system_ps = OS.Process.system
end;

(* (2) quote-filter modules. *)
pr "\nMETIS_FILTER_START\n";
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

(* helpers: string replace; patch-then-quote-filter a HOL .sml. *)
fun rs (s, f, r) =
    let val (p,sf) = Substring.position f (Substring.full s)
    in if Substring.isEmpty sf then s
       else Substring.string p ^ r ^ Substring.string (Substring.triml (size f) sf) end;
fun writeFile (p, s) = let val os = TextIO.openOut p in TextIO.output(os,s); TextIO.closeOut os end;
fun filterFileHOL (src, outp, edits) =
    let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/" ^ src))
        val patched = foldl (fn ((f,r),acc) => rs(acc,f,r)) raw edits
        val tmp = outp ^ ".pre"
        val () = writeFile (tmp, patched)
        val filtered = HOLSource.inputFile {quietOpen=false, print=fn _ => ()} tmp
    in writeFile (outp, filtered); outp end;

(* Script->Theory: filter, neutralize export, use, synthesize structure. *)
fun validName s =
    size s > 0 andalso Char.isAlpha (String.sub(s,0)) andalso
    CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_" orelse c = #"'") s;
val thmTbl = ref ([] : (string * Thm.thm) list);
fun thmLookup n = #2 (valOf (List.find (fn (m,_) => m = n) (!thmTbl)));
fun synthTheory (scriptRel, structName, genPath) =
    let val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()} (HOL ^ "/" ^ scriptRel)
        val (pre,suf) = Substring.position "export_theory" (Substring.full raw)
        val neut = Substring.string pre ^ "current_theory"
                   ^ Substring.string (Substring.triml (size "export_theory") suf)
        val stmp = genPath ^ ".script"
        val () = writeFile (stmp, neut)
        val () = PolyML.use stmp
        val named = Theory.current_axioms() @ Theory.current_definitions()
                    @ Theory.current_theorems()
        val seen = ref ([] : string list)
        val () = thmTbl := []
        val () = app (fn (n,th) =>
                       if validName n andalso not (List.exists (fn m => m = n) (!seen))
                       then (seen := n :: !seen; thmTbl := (n,th) :: !thmTbl) else ())
                     named
        val () = let val os = TextIO.openOut genPath
                 in TextIO.output(os, "structure " ^ structName ^ " = struct\n");
                    app (fn (n,_) => TextIO.output(os, "  val " ^ n ^ " = thmLookup \"" ^ n ^ "\";\n"))
                        (!thmTbl);
                    TextIO.output(os, "end;\n"); TextIO.closeOut os
                 end
        val cnt = length (!thmTbl)
    in PolyML.use genPath; cnt end;

(* (3) replay the taut layer (so Canon/normalForms, which open tautLib, load). *)
val () = ignore (synthTheory ("src/HolSat/satScript.sml", "satTheory", "/tmp/satTheory_gen.sml"))
         handle e => pr ("SATTHEORY_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr ("SATTHEORY_NAMES " ^ Int.toString (length (!thmTbl)) ^ "\n");
structure computeLib = struct
  val EVAL_CONV : Term.term -> Thm.thm =
      fn _ => raise Fail "computeLib.EVAL_CONV stub (SAT/cex path unused)"
end;
structure minisatParse = struct
  fun replayProof _ _ _ _ _ _ _ _ = (NONE : Thm.thm option)
end;
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
val () = pr ("HOLSAT_LOADED " ^ Int.toString hcount ^ "/" ^ Int.toString (length holsatFiles) ^ "\n");
(* tautLib.sml has no term quotations — patch raw (no quote-filter needed). *)
val () = (let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/src/taut/tautLib.sml"))
              val p1 = rs(raw, "val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}", "val bool_grammars = ()")
              val p2 = rs(p1, "val (Type,Term) = parse_from_grammars bool_grammars", "val (Type,Term) = (Parse.Type, Parse.Term)")
          in writeFile ("/tmp/tautLib_patched.sml", p2) end);
val _ = useHOL "src/taut/tautLib.sig";
val () = (PolyML.use "/tmp/tautLib_patched.sml"; pr "TAUTLIB_LOADED\n")
         handle e => pr ("TAUTLIB_FAIL :: " ^ exnMessage e ^ "\n");

(* (4) portableML prereqs for mlib (Intmap + Random; harmless if already present). *)
val _ = useHOL "src/portableML/poly/Intmap.sig";
val _ = useHOL "src/portableML/poly/Intmap.sml";
val _ = useHOL "src/portableML/poly/Intset.sig";
val _ = useHOL "src/portableML/poly/Intset.sml";
val _ = useHOL "src/portableML/poly/Random.sig";
val _ = useHOL "src/portableML/poly/Random.sml";

(* (5) the mlib core, 33 modules in dependency order (sig then sml). *)
pr "MLIB_LOAD_START\n";
val mlibMods = [
  "mlibPortable","mlibUseful","mlibMeter","mlibMultiset","mlibStream","mlibHeap",
  "mlibParser","mlibTerm","mlibModel","mlibSubst","mlibCanon","mlibKernel",
  "mlibMatch","mlibTermnet","mlibLiteralnet","mlibSubsume","mlibThm","mlibRewrite",
  "mlibArbnum","mlibArbint","mlibOmegaint","mlibPatricia","mlibOmega","mlibTermorder",
  "mlibTptp","mlibUnits","mlibClause","mlibClauseset","mlibSolver","mlibMeson",
  "mlibSupport","mlibResolution","mlibMetis"
];
val mcount = foldl (fn (m,a) =>
    let val s = useHOL ("src/metis/" ^ m ^ ".sig")
        val b = useHOL ("src/metis/" ^ m ^ ".sml")
    in if b then a+1 else a end) 0 mlibMods;
val () = pr ("MLIB_LOADED " ^ Int.toString mcount ^ "/" ^ Int.toString (length mlibMods) ^ "\n");

(* (6) HOL glue. *)
pr "GLUE_LOAD_START\n";
(* Canon (src/refute) — quotations + grammarDB{combin}. *)
val canonF = filterFileHOL ("src/refute/Canon.sml", "/tmp/refuteCanon_filtered.sml",
  [("val combin_grammars = Option.valOf $ grammarDB {thyname=\"combin\"}", "val combin_grammars = Parse.current_grammars()"),
   ("val _ = Parse.temp_set_grammars combin_grammars", "val _ = ()")]);
val _ = useHOL "src/refute/Canon.sig";
val () = (PolyML.use canonF; pr "CANON_OK\n") handle e => pr ("CANON_FAIL :: " ^ exnMessage e ^ "\n");

val _ = useHOL "src/metis/matchTools.sig";
val () = (PolyML.use (HOL ^ "/src/metis/matchTools.sml"); pr "MATCHTOOLS_OK\n")
         handle e => pr ("MATCHTOOLS_FAIL :: " ^ exnMessage e ^ "\n");

val fmF = filterFileHOL ("src/metis/folMapping.sml", "/tmp/folMapping_filtered.sml", []);
val _ = useHOL "src/metis/folMapping.sig";
val () = (PolyML.use fmF; pr "FOLMAPPING_OK\n")
         handle e => pr ("FOLMAPPING_FAIL :: " ^ exnMessage e ^ "\n");

(* bool_ss closure — normalForms's load-time proofs use SIMP_TAC boolSimps.bool_ss.
   Trace/Cond_rewr/AC/Ho_Rewrite already present (from the simp build); refuteLib
   needs Canon (loaded above). pureSimps/refuteLib are plain; BoolExtractShared/
   Unwind/boolSimps carry quotations -> quote-filter. *)
val _ = useHOL "src/simp/src/pureSimps.sig";
val () = (PolyML.use (HOL ^ "/src/simp/src/pureSimps.sml"); pr "PURESIMPS_OK\n")
         handle e => pr ("PURESIMPS_FAIL :: " ^ exnMessage e ^ "\n");
val _ = useHOL "src/refute/refuteLib.sig";
val () = (PolyML.use (HOL ^ "/src/refute/refuteLib.sml"); pr "REFUTELIB_OK\n")
         handle e => pr ("REFUTELIB_FAIL :: " ^ exnMessage e ^ "\n");
val besF = filterFileHOL ("src/1/BoolExtractShared.sml", "/tmp/BoolExtractShared_filtered.sml", []);
val _ = useHOL "src/1/BoolExtractShared.sig";
val () = (PolyML.use besF; pr "BOOLEXTRACT_OK\n") handle e => pr ("BOOLEXTRACT_FAIL :: " ^ exnMessage e ^ "\n");
val unwF = filterFileHOL ("src/simp/src/Unwind.sml", "/tmp/Unwind_filtered.sml", []);
val _ = useHOL "src/simp/src/Unwind.sig";
val () = (PolyML.use unwF; pr "UNWIND_OK\n") handle e => pr ("UNWIND_FAIL :: " ^ exnMessage e ^ "\n");
(* extend the checkpoint's markerLib stub with TIDY_ABBREV_CONV (boolSimps' ABBREV_ss
   conv; a no-op suffices — Abbrev markers do not appear in normalForms' load proofs). *)
structure markerLib = struct
  open markerLib
  val TIDY_ABBREV_CONV : Term.term -> Thm.thm = fn _ => raise Conv.UNCHANGED
  (* real Cong (markerLib.sml:77); our stub raised. markerTheory present. *)
  fun Cong th = Thm.EQ_MP (Thm.SYM (Thm.SPEC (Thm.concl th) markerTheory.Cong_def)) th
end;
(* boolSimps' BOOL_ss does DB.fetch "bool" NAME for ~20 standard bool theorems;
   our checkpoint DB is a stub that raises. Shadow DB.fetch with a table over the
   synthesized boolTheory so those lookups succeed. *)
structure DB = struct
  open DB
  val boolThms : (string * Thm.thm) list = [
    ("REFL_CLAUSE", boolTheory.REFL_CLAUSE), ("EQ_CLAUSES", boolTheory.EQ_CLAUSES),
    ("NOT_CLAUSES", boolTheory.NOT_CLAUSES), ("AND_CLAUSES", boolTheory.AND_CLAUSES),
    ("OR_CLAUSES", boolTheory.OR_CLAUSES), ("IMP_CLAUSES", boolTheory.IMP_CLAUSES),
    ("COND_CLAUSES", boolTheory.COND_CLAUSES), ("FORALL_SIMP", boolTheory.FORALL_SIMP),
    ("EXISTS_SIMP", boolTheory.EXISTS_SIMP), ("COND_ID", boolTheory.COND_ID),
    ("EXISTS_REFL", boolTheory.EXISTS_REFL), ("EXISTS_UNIQUE_REFL", boolTheory.EXISTS_UNIQUE_REFL),
    ("EXCLUDED_MIDDLE", boolTheory.EXCLUDED_MIDDLE), ("bool_case_thm", boolTheory.bool_case_thm),
    ("NOT_AND", boolTheory.NOT_AND), ("SELECT_REFL", boolTheory.SELECT_REFL),
    ("SELECT_REFL_2", boolTheory.SELECT_REFL_2), ("RES_FORALL_TRUE", boolTheory.RES_FORALL_TRUE),
    ("RES_EXISTS_FALSE", boolTheory.RES_EXISTS_FALSE), ("EXISTS_UNIQUE_FALSE", boolTheory.EXISTS_UNIQUE_FALSE)];
  fun fetch "bool" s =
        (case List.find (fn (n,_) => n = s) boolThms of
             SOME (_,th) => th
           | NONE => DB.fetch "bool" s)
    | fetch thy s = DB.fetch thy s
end;
val bssF = filterFileHOL ("src/simp/src/boolSimps.sml", "/tmp/boolSimps_filtered.sml",
  [("val SOME combin_grammars = grammarDB {thyname=\"combin\"}", "val combin_grammars = Parse.current_grammars()"),
   ("val _ = Parse.temp_set_grammars combin_grammars", "val _ = ()")]);
val _ = useHOL "src/simp/src/boolSimps.sig";
val () = (PolyML.use bssF; pr "BOOLSIMPS_OK\n") handle e => pr ("BOOLSIMPS_FAIL :: " ^ exnMessage e ^ "\n");

(* normalFormsTheory via the Script->Theory recipe. *)
val () = (let val n = synthTheory ("src/metis/normalFormsScript.sml", "normalFormsTheory",
                                   "/tmp/normalFormsTheory_gen.sml")
          in pr ("NORMALFORMS_NAMES " ^ Int.toString n ^ "\n") end)
         handle e => pr ("NORMALFORMSTHEORY_FAIL :: " ^ exnMessage e ^ "\n");

(* normalForms — quotations + grammarDB{combin}. *)
val nfF = filterFileHOL ("src/metis/normalForms.sml", "/tmp/normalForms_filtered.sml",
  [("val SOME combin_grammars = grammarDB {thyname=\"combin\"}", "val combin_grammars = Parse.current_grammars()"),
   ("val (Type,Term) = parse_from_grammars combin_grammars", "val (Type,Term) = (Parse.Type, Parse.Term)")]);
val _ = useHOL "src/metis/normalForms.sig";
val () = (PolyML.use nfF; pr "NORMALFORMS_OK\n") handle e => pr ("NORMALFORMS_FAIL :: " ^ exnMessage e ^ "\n");

(* folTools — quotations + grammarDB{normalForms}. *)
val ftF = filterFileHOL ("src/metis/folTools.sml", "/tmp/folTools_filtered.sml",
  [("val SOME normalForms_grammars = grammarDB {thyname=\"normalForms\"}", "val normalForms_grammars = Parse.current_grammars()"),
   ("val (Type,Term) = parse_from_grammars normalForms_grammars", "val (Type,Term) = (Parse.Type, Parse.Term)")]);
val _ = useHOL "src/metis/folTools.sig";
val () = (PolyML.use ftF; pr "FOLTOOLS_OK\n") handle e => pr ("FOLTOOLS_FAIL :: " ^ exnMessage e ^ "\n");

val _ = useHOL "src/metis/metisTools.sig";
val () = (PolyML.use (HOL ^ "/src/metis/metisTools.sml"); pr "METISTOOLS_OK\n")
         handle e => pr ("METISTOOLS_FAIL :: " ^ exnMessage e ^ "\n");
val _ = useHOL "src/metis/metisLib.sig";
val () = (PolyML.use (HOL ^ "/src/metis/metisLib.sml"); pr "METISLIB_OK\n")
         handle e => pr ("METISLIB_FAIL :: " ^ exnMessage e ^ "\n");

(* (7) METIS smoke — equality/paramodulation goals (where METIS beats MESON). *)
val () = (Feedback.set_trace "metis" 0) handle _ => ();
val () = (mlibUseful.trace_level := 0) handle _ => ();
val smoke = ref true;
fun metis tag s =
    let val g = Parse.Term [QUOTE s]
        val th = Tactical.prove(g, metisLib.METIS_TAC [])
    in pr ("METIS " ^ tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
       if null (Thm.hyp th) andalso Term.aconv (Thm.concl th) g then ()
       else smoke := false
    end handle e => (smoke := false; pr ("METIS_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
(* right-identity and right-inverse from the LEFT group axioms (pure equational,
   needs paramodulation) and a comm+assoc chain reversal. *)
val () = metis "GRP_RID" "(!x. mul e x = x) /\\ (!x. mul (i x) x = e) /\\ (!x y z. mul (mul x y) z = mul x (mul y z)) ==> (!x. mul x e = x)";
val () = metis "GRP_RINV" "(!x. mul e x = x) /\\ (!x. mul (i x) x = e) /\\ (!x y z. mul (mul x y) z = mul x (mul y z)) ==> (!x. mul x (i x) = e)";
val () = metis "AC_CHAIN" "(!x y. mul x y = mul y x) /\\ (!x y z. mul (mul x y) z = mul x (mul y z)) ==> mul (mul (mul a b) c) d = mul d (mul c (mul b a))";
val () = pr (if !smoke then "METIS_SMOKE_PASS\n" else "METIS_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_metis\n";
       PolyML.export("/tmp/hol4_metis", PolyML.rootFunction);
       pr "METIS_CHECKPOINT_DONE\n")
    else pr "METIS_CHECKPOINT_SKIPPED (smoke failed)\n";
