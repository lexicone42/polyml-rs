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
      "([] : Thm.thm list)")])];

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
  (* the small set TFL/TotalDefn actually call; the heavy registry/congruence
     machinery (read_congs/write_congs/...) is stubbed since Define's core
     path on simple defns doesn't consult it. *)
  fun register_indn (_ : Thm.thm * Term.term list) : unit = ()
  val tupled_suffix = "_tupled"
  fun delete_support (_ : Term.term list) : unit = ()
  fun constants_of_defn (tm : Term.term) : Term.term list =
      HolKernel.find_terms Term.is_const tm
  (* registration no-ops referenced by sum/option/basicSize Scripts *)
  fun store (_ : string * Thm.thm * Thm.thm) : unit = ()
  fun read_congs () : Thm.thm list = []
  fun write_congs (_ : Thm.thm list) : unit = ()
  fun add_cong (_ : Thm.thm) : unit = ()
  fun register_defn _ : unit = ()
  fun export_cong (_ : string) : unit = ()
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

(* ---- Phase 7: TFL core (needs pairLib; NOT the size theories). Defn.Hol_defn
   is the low-level definition mechanism; TotalDefn.Define wraps it with
   automatic termination. ---- *)
pr "PHASE7_TFL\n";
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
