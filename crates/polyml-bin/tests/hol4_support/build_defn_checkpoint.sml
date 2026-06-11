(* build_defn_checkpoint.sml — Stage 6b: the TFL / Define stack on
   /tmp/hol4_pair, exported as /tmp/hol4_defn.

   Dependency closure (mapped 2026-06-11):
     real DefnBase (DefnBaseCore + DefnBase, replacing our long stub)
     -> pairLib SML stack (pairSyntax/PairRules/PairedLambda/pairTools/pairLib)
     -> oneTheory, sumTheory, optionTheory, basicSizeTheory (Script->Theory)
     -> TFL core (wfrecUtils/Rules/Induction/Extract/Defn)
     -> TotalDefn  ==>  Define / xDefine / tDefine / qDefine

   This phase (v1) loads the SML LIB foundation only (DefnBase + pairLib);
   the theory builds + TFL follow once this compiles.

   Usage (cwd = vendor/polyml):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 2000000000000 \
       /tmp/hol4_pair crates/polyml-bin/tests/hol4_support/build_defn_checkpoint.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
infix THEN THENL THEN1 ORELSE;
pr "\nDEFN_BUILD_START\n";
val () = Globals.interactive := true;

fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;
fun fileExists p =
    (let val is = TextIO.openIn p in TextIO.closeIn is; true end) handle _ => false;
fun replaceAll (s, old, new) =
    let val (pre, suf) = Substring.position old (Substring.full s)
    in if Substring.size suf = 0 then s
       else Substring.string pre ^ new
            ^ replaceAll (Substring.string (Substring.triml (size old) suf), old, new)
    end;

(* per-module post-filter patches *)
val modPatches : (string * (string * string) list) list =
  [(* pairLib registers let-simp thms via BasicProvers.new_let_thms (we no-op
      it); the 4 *_UNCURRY* thms are unswept pairTheory niceties — drop the
      list so the no-op call still type-checks. *)
   ("pairLib",
    (* filter spaces the list: `[ o_UNCURRY_R , C_UNCURRY_L , ... ]` *)
    [("[ o_UNCURRY_R , C_UNCURRY_L , S_UNCURRY_R , FORALL_UNCURRY ]",
      "([] : Thm.thm list)")]),
   (* Extract: grammarDB returns NONE for ancestor segments -> valOf raises
      Option. Current grammars ARE bool's on this image. *)
   ("Extract",
    [("valOf $ grammarDB { thyname = \"bool\" }", "Parse.current_grammars ()"),
     ("valOf $ grammarDB {thyname=\"bool\"}", "Parse.current_grammars ()")]),
   (* proofManagerLib installs an LSP dump hook absent from our boolLib;
      the hook is cosmetic (proof-state dumping). *)
   ("proofManagerLib",
    [("val _ = boolLib.dump_setup_hook := ( fn g => ignore ( set_goal g ) )",
      "val _ = ()"),
     ("boolLib.dump_setup_hook := (fn g => ignore (set_goal g))", "()")]),
   (* Defn/TotalDefn: DB.Unknown (thm_src_location) — our baked DB shadow
      lacks it; reference DB_dtype.Unknown directly. *)
   ("Defn",
    [("DB.Unknown", "DB_dtype.Unknown")]),
   ("TotalDefn",
    [("DB.Unknown", "DB_dtype.Unknown"),
     ("val SOME arithmetic_grammars = grammarDB { thyname = \"arithmetic\" }",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     ("val SOME arithmetic_grammars = grammarDB {thyname=\"arithmetic\"}",
      "val arithmetic_grammars = Parse.current_grammars ()"),
     (* the initial termsimp set registers 9 rewrites BY NAME
        (temp_export_termsimp "combin.o_DEF" -> DB.fetch, which our baked DB
        stub raises). Skip the by-name pre-load: a no-op List.app leaves the
        termsimp set with just its `initial` thms — degrades TC simplification
        only (ARITH_ss still discharges the num TCs). *)
     ("List.app temp_export_termsimp", "List.app (fn _ => ())")])];

fun useFilt path =
    let val name = List.last (String.fields (fn c => c = #"/") path)
        val sigf = path ^ ".sig"
        val smlf = path ^ ".sml"
    in
      if not (fileExists smlf) then (pr ("DF_MISSING " ^ name ^ "\n"); false)
      else
        ((if fileExists sigf then (PolyML.use sigf handle _ => ()) else ();
          let val txt0 = HOLSource.inputFile {quietOpen = false, print = fn _ => ()} smlf
              val txt = case List.find (fn (n,_) => n = name) modPatches of
                            NONE => txt0
                          | SOME (_, ps) =>
                              List.foldl (fn ((a,b),t) => replaceAll (t,a,b)) txt0 ps
          in writeFile ("/tmp/df_filtered.sml", txt); PolyML.use "/tmp/df_filtered.sml" end;
          pr ("DF_OK   " ^ name ^ "\n"); true)
         handle e => (pr ("DF_FAIL " ^ name ^ " :: " ^
                          (case e of Fail m => m | _ => exnMessage e) ^ "\n"); false))
    end;

(* ---- Phase 0: prelude. The REAL DefnBase/DefnBaseCore pull in the DB
   definition-registry + LSPExtension/ThreadLocal infra our stubs don't model.
   TFL/TotalDefn only CALL 4 DefnBase functions (register_indn/tupled_suffix/
   delete_support/constants_of_defn) — hand-roll those (markerLib pattern) and
   stub the rest. (TypeBasePure is the REAL one — loaded in Phase 1.) ---- *)
pr "PHASE0_PRELUDE\n";
structure DefnBase = struct
  (* the `defn` datatype IS exported here (Defn.sml does `open DefnBase` for
     the constructors; Defn.sig has `type defn = DefnBase.defn`). Copied
     verbatim from src/coretypes/DefnBase.sml:14. *)
  type term = Term.term
  type thm = Thm.thm
  datatype defn
     = ABBREV  of {eqn:thm, bind:string}
     | PRIMREC of {eqs:thm, ind:thm, bind:string}
     | NONREC  of {eqs:thm, ind:thm, SV:term list, stem:string}
     | STDREC  of {eqs:thm list, ind:thm, R:term, SV:term list, stem:string}
     | MUTREC  of {eqs:thm list, ind:thm, R:term, SV:term list,
                   stem:string, union:defn}
     | NESTREC of {eqs:thm list, ind:thm, R:term, SV:term list,
                   stem:string, aux:defn}
     | TAILREC of {eqs:thm list, ind:thm, R:term, SV:term list, stem:string}
  type kname = {Thy:string, Name:string}
  (* the small set TFL/TotalDefn CALL; the heavy registry/congruence machinery
     (read_congs/write_congs/...) is stubbed — Define's core path on simple
     defns doesn't consult it (just registration side effects). *)
  val tupled_suffix = "_tupled"
  fun register_indn (_ : thm * kname list) : unit = ()
  fun delete_support (_ : defn) (_ : term list) (_ : term list) : unit = ()
  fun constants_of_defn (_ : thm) : kname list = []
  (* registration no-ops referenced by sum/option/basicSize Scripts *)
  fun store (_ : string * thm * thm) : unit = ()
  fun read_congs () : thm list = []
  fun write_congs (_ : thm list) : unit = ()
  fun add_cong (_ : thm) : unit = ()
  fun register_defn _ : unit = ()
  fun export_cong (_ : string) : unit = ()
  (* elim_triv_literal_CONV + const_eq_ref: copied verbatim from
     src/coretypes/DefnBase.sml:233 (Defn.sml uses it via `open DefnBase`).
     boolLib re-exports TRY_CONV/REWR_CONV/THENC/BETA_CONV/RATOR_CONV/
     RAND_CONV/PURE_ONCE_REWRITE_CONV. *)
  val const_eq_ref = ref Conv.NO_CONV
  local open boolLib infix THENC in
  fun elim_triv_literal_CONV tm =
     let val const_eq_conv = !const_eq_ref
         val cnv = TRY_CONV (REWR_CONV boolTheory.literal_case_THM THENC BETA_CONV)
                   THENC
                   RATOR_CONV (RATOR_CONV (RAND_CONV const_eq_conv))
                   THENC
                   PURE_ONCE_REWRITE_CONV [boolTheory.COND_CLAUSES]
     in cnv tm end
  end
end;


(* variant_of_term: a boolLib fn absent from our checkpoint's boolLib
   (pairTools/pairLib call it unqualified via `open boolLib`); copied verbatim
   from src/1/boolLib.sml:388. Top-level so it's visible inside those units. *)
val variant_of_term =
  fn vs => fn t =>
    let open HolKernel
        val check_vars = free_vars t
        val (_, sub) =
            foldl (fn (v, (vs, sub)) =>
                      let val v' = variant vs v
                          val vs' = v' :: vs
                          val sub' = if aconv v v' then sub else (v |-> v') :: sub
                      in (vs', sub') end) (vs, []) check_vars
    in (subst sub t, sub) end;

(* BasicProvers.new_let_thms: registers let-normalisation rewrites; a no-op is
   fine (the let-simp is a convenience, not on Define's core path). *)
structure BasicProvers = struct
  open BasicProvers
  fun new_let_thms (_ : Thm.thm list) : unit = ()
  (* thy_ssfrag s = simpset frag from thy's registered simp-deltas; our shim
     tracks none, so an empty frag (pairSimps' PAIR_ss becomes empty — fine,
     the structural pair rewrites live in pairTheory regardless). *)
  fun thy_ssfrag (_ : string) : simpLib.ssfrag = simpLib.rewrites []
  (* PRIM_STP_TAC ss finisher: simp-then-prove. TotalDefn uses it (after a
     SIMP_CONV) to discharge termination conditions; ASM_SIMP + the finisher
     is enough for the simple TCs (n < SUC n etc.) ARITH_ss reduces. *)
  fun PRIM_STP_TAC (ss : simpLib.simpset) (finisher : Abbrev.tactic)
                 : Abbrev.tactic =
      Tactical.THEN (simpLib.ASM_SIMP_TAC ss [],
                     Tactical.ORELSE (finisher, Tactical.ALL_TAC))
end;

(* tailrecLib: only TotalDefn.tailrecDefine (the [tailrecursive] attribute
   path) calls gen_tailrec_define; normal Define never does. Stub it. *)
structure tailrecLib = struct
  fun gen_tailrec_define
        (_ : {name:string, def:Term.term, loc:DB_dtype.thm_src_location})
        : Thm.thm = raise Fail "tailrecLib stub (no [tailrecursive] support)"
end;
val () = pr "PRELUDE_OK\n";

(* ---- Phase 1: the REAL TypeBase infrastructure (replaces our long-standing
   stub). Clean bounded closure: PmatchHeuristics -> Pmatch -> TypeBasePure ->
   TypeBase. TFL's Induction consults TypeBasePure.nchotomy_of/prim_get for
   case-split + induction theorems; an empty stub returns nothing, so we need
   the real registry (then register num/pair into it in Phase 6). ---- *)
pr "PHASE1_TYPEBASE\n";
val one = HOL ^ "/src/1/";
val _ = useFilt (one ^ "PmatchHeuristics");
val _ = useFilt (one ^ "Pmatch");
val _ = useFilt (one ^ "TypeBasePure");
val _ = useFilt (one ^ "TypeBase");

(* ---- Phase 2: pairLib SML stack ---- *)
pr "PHASE2_PAIRLIB\n";
val ct = HOL ^ "/src/coretypes/";
val _ = useFilt (ct ^ "pairSyntax");
val _ = useFilt (ct ^ "PairedLambda");   (* PairRules uses it (qualified) *)
val _ = useFilt (ct ^ "PairRules");
val _ = useFilt (ct ^ "pairTools");
val _ = useFilt (ct ^ "pairSimps");      (* pairLib opens it *)
val _ = useFilt (ct ^ "pairLib");

val () = pr "DEFN_PHASE12_DONE\n";

(* ---- Phase 5: basicSizeTheory, built INLINE now that pairLib's
   new_definition_hook is installed (paired (x,y) defs work). ---- *)
pr "PHASE5_BASICSIZE\n";
val _ = (PolyML.use (HOL ^ "/../../crates/polyml-bin/tests/hol4_support/basicsize_inline.sml");
         pr "BASICSIZE_DONE\n")
        handle e => pr ("BASICSIZE_FAIL :: " ^ exnMessage e ^ "\n");

(* ---- Phase 3: sum/basicSize term syntax (the theories are baked into the
   base image by the sum/option sweeps; here we load the SML syntax libs
   Defn/TotalDefn need). ---- *)
pr "PHASE3_SYNTAX\n";
val _ = useFilt (ct ^ "sumSyntax");
val _ = useFilt (HOL ^ "/src/combin/combinSyntax");  (* Defn uses it *)
val _ = useFilt (HOL ^ "/src/num/theories/basicSizeSyntax");

(* ---- Phase 4: proofman subsystem (Defn's interactive tgoal/tprove path uses
   Manager + proofManagerLib; needed only to COMPILE Defn). Order found by
   '^open': History -> goalStack -> goalFrag -> goalTree -> Manager ->
   proofManagerLib. ---- *)
pr "PHASE4_PROOFMAN\n";
val pm = HOL ^ "/src/proofman/";
val _ = useFilt (pm ^ "History");
val _ = useFilt (pm ^ "goalStack");
val _ = useFilt (pm ^ "goalFrag");
val _ = useFilt (pm ^ "goalTree");
val _ = useFilt (pm ^ "Manager");
val _ = useFilt (pm ^ "proofManagerLib");

(* ---- Phase 7: TFL core (needs pairLib + real TypeBase + sumSyntax + Manager).
   Defn.Hol_defn is the low-level definition mechanism; TotalDefn.Define wraps
   it with automatic termination. ---- *)
pr "PHASE7_TFL\n";
(* DB shadow: Unknown (thm_src_location, for Defn's store_at) + a real fetch.
   ThmSetData.lookup_exn calls DB.fetch <thy> <name> while restoring saved
   set-data at TotalDefn load (e.g. combin$o_DEF in combin's simp set); the
   baked stub raises. Serve the known ones; log + return TRUTH for the rest
   so restoration continues (a T-rewrite is a no-op, not corruption).
   Shadowed HERE so no intervening module reshadows DB before Defn/TotalDefn. *)
structure DB = struct
  open DB
  val Unknown = DB_dtype.Unknown
  val fetchTable : (string * string * Thm.thm) list =
    [("combin", "o_DEF", combinTheory.o_DEF),
     ("combin", "I_THM", combinTheory.I_THM),
     ("combin", "K_THM", combinTheory.K_THM),
     ("combin", "S_DEF", combinTheory.S_DEF),
     ("bool", "LET_DEF", boolTheory.LET_DEF)]
  fun fetch thy nm =
      case List.find (fn (t, n, _) => t = thy andalso n = nm) fetchTable of
          SOME (_, _, th) => th
        | NONE => (pr ("DB_FETCH_MISS " ^ thy ^ "." ^ nm ^ "\n"); boolTheory.TRUTH)
end;
val tfl = HOL ^ "/src/tfl/src/";
val _ = useFilt (tfl ^ "wfrecUtils");
val _ = useFilt (tfl ^ "Rules");
val _ = useFilt (tfl ^ "Induction");
val _ = useFilt (tfl ^ "Extract");
val _ = useFilt (tfl ^ "Defn");

fun need tag b = pr ((if b then "OK " else "MISSING ") ^ tag ^ "\n");
val () = need "pairLib" ((ignore (PolyML.makestring pairLib.PAIRED_BETA_CONV); true) handle _ => false);
val () = need "Defn"    ((ignore (PolyML.makestring Defn.Hol_defn); true) handle _ => false);
val () = pr "DEFN_PHASE7_DONE\n";

(* ---- Phase 8: TotalDefn (defines Define). Needs basicSize/DefnBase/numSyntax/
   simpLib. ---- *)
pr "PHASE8_TOTALDEFN\n";
(* measure_def/WF_measure/measure_thm/WF_PRED (cut with the prim_rec WF tail)
   + the `basicSize` alias TotalDefn opens. *)
val _ = (PolyML.use (HOL ^ "/../../crates/polyml-bin/tests/hol4_support/measure_frag.sml");
         pr "MEASURE_DONE\n")
        handle e => pr ("MEASURE_FAIL :: " ^ exnMessage e ^ "\n");
structure basicSize = basicSizeTheory;
val _ = useFilt (HOL ^ "/src/num/termination/TotalDefn");
val () = need "TotalDefn-Define"
              ((ignore (PolyML.makestring TotalDefn.Define); true) handle _ => false);

(* smoke: actually DEFINE something. Non-recursive first (no termination),
   then a structural recursion over num. *)
val smoke = ref true;
fun trySmoke tag f = (f (); pr ("SMOKE_OK " ^ tag ^ "\n"))
                     handle e => (smoke := false;
                                  pr ("SMOKE_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
(* backticks aren't parsed by our interpreter (the quote-filter normally
   expands them); hand-build the term-quotation frag list directly. *)
val () = trySmoke "Define-nonrec" (fn () =>
    ignore (TotalDefn.Define [QUOTE "dbl x = x + x"]));
val () = trySmoke "Define-rec" (fn () =>
    ignore (TotalDefn.Define
              [QUOTE "(sumto 0 = 0) /\\ (sumto (SUC n) = SUC n + sumto n)"]));
val () = pr (if !smoke then "DEFN_SMOKE_PASS\n" else "DEFN_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_defn\n";
       PolyML.export ("/tmp/hol4_defn", PolyML.rootFunction);
       pr "DEFN_CHECKPOINT_DONE\n")
    else pr "DEFN_EXPORT_SKIPPED\n";
