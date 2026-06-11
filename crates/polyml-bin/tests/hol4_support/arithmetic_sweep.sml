(* arithmetic_sweep.sml — Stage 4: sweep the REAL arithmeticScript.sml
   (5759 lines, 524 Theorem blocks) per-theorem on /tmp/hol4_relation and
   export /tmp/hol4_arithmetic. Same harness as relation_tail_sweep with:
     * sweep from line 1 (chunk 0 = the Theory header: new_theory + opens);
     * a REBIND shim injected right after the header chunk — the header's
       `open boolLib BasicProvers ...` spills the image's OLD bindings over
       the driver's fixes (the unqualified-name lesson from relation);
     * Cases_on knows num (STRUCT_CASES via the in-script num_CASES, looked
       up dynamically) and bool (ASM_CASES); Induct_on knows num
       (ID_SPEC_TAC + INDUCT_THEN numTheory.INDUCTION) + rule-induction;
     * DefnBase stub (qualified-open only, zero direct uses).
   Fail-and-continue: one run = the complete OK/FAIL map; METIS chunks that
   die (the known mlib time-slice flakiness) just log and can re-run later.

   Usage (cwd = vendor/polyml):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 3000000000000 \
       /tmp/hol4_relation crates/polyml-bin/tests/hol4_support/arithmetic_sweep.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
infix THEN THENL THEN1 ORELSE;
infix 8 by;

pr "\nARITHMETIC_SWEEP_START\n";
val () = Globals.interactive := true;
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax; pr ("REG_AX " ^ nm ^ "\n"))
            handle _ => pr ("REG_AX_NOTE " ^ nm ^ " (already)\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];

structure DefnBase = struct end;

(* ---- the fixed tactic/store layer (rebound via the injected shim too) ---- *)
structure boolLib = struct
  open boolLib
  fun save_thm_at _ (n, th) =
      Theory.save_thm (hd (String.fields (fn c => c = #"[") n), th)
  fun new_definition (n, tm) =
      Theory.Definition.new_definition
        (hd (String.fields (fn c => c = #"[") n), tm)
end;

structure BasicProvers = struct
  open BasicProvers
  (* THE checkpoint-wide root (fleet diagnosis): our markerLib stub's
     process_taclist_then drops `map ASSUME asl`, so simpLib.ASM_SIMP_TAC
     has been silently identical to SIMP_TAC since the simp build — every
     inductive proof closing with ASM_SIMP+IH failed. Inject the
     assumptions ourselves. *)
  fun ASM_SIMP_TAC ss thl (g as (asl, _)) =
      simpLib.SIMP_TAC ss (List.map Thm.ASSUME asl @ thl) g
  fun FULL_SIMP_TAC ss thl =
      Tactical.THEN (simpLib.FULL_SIMP_TAC ss thl,
                     Tactical.TRY (ASM_SIMP_TAC ss thl))
  val closer =
      Tactical.TRY (Tactical.THEN (Rewrite.ONCE_ASM_REWRITE_TAC [],
        Tactical.THEN (Rewrite.REWRITE_TAC [], Tactical.NO_TAC)))
  fun RW_TAC ss thl =
      Tactical.THEN (Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
        FULL_SIMP_TAC ss thl), closer)
  val rw_tac = RW_TAC
  fun SRW_TAC frags thl =
      RW_TAC (List.foldl (fn (f, ss) => simpLib.++ (ss, f)) (srw_ss ()) frags) thl
  fun simp thl = ASM_SIMP_TAC (srw_ss ()) thl
  fun SPOSE_NOT_THEN ttac =
      Tactical.THEN (Tactic.CCONTR_TAC,
        Tactical.POP_ASSUM (fn th =>
          ttac (simpLib.SIMP_RULE boolSimps.bool_ss
                  [Conv.GSYM boolTheory.IMP_DISJ_THM] th)))
  fun parse_ctxt q (asl, w) =
      Parse.parse_in_context (Term.free_varsl (w :: asl)) q
  val numty = Type.mk_thy_type {Thy = "num", Tyop = "num", Args = []}
  fun current_thm nm =
      Option.map #2 (List.find (fn (n, _) => n = nm) (Theory.current_theorems ()))
  fun Cases_on q (g as (asl, w)) =
      let val tm = parse_ctxt q g
          val ty = Term.type_of tm
      in
        if ty = Type.bool then Tactic.ASM_CASES_TAC tm g
        else if ty = numty then
          (case current_thm "num_CASES" of
               SOME th => Tactic.FULL_STRUCT_CASES_TAC (Thm.SPEC tm th) g
             | NONE => raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Cases_on"
                             "num_CASES not yet proved")
        else raise Feedback.mk_HOL_ERR "BasicProvers(shim)" "Cases_on"
                   "only bool/num supported"
      end
  fun Induct_on q (g as (asl, w)) =
      let val tm = parse_ctxt q g
          val ty = Term.type_of tm
      in
        if ty = numty then
          Tactical.THEN (Q.ID_SPEC_TAC q,
            Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC) g
        else
          let val (c, _) = boolSyntax.strip_comb tm
              val {Thy, Name, ...} = Term.dest_thy_const c
              val ths = Option.getOpt
                          (KNametab.lookup (IndDefLib.rule_induction_map ())
                                           {Thy = Thy, Name = Name}, [])
              fun try [] = raise Feedback.mk_HOL_ERR "BasicProvers(shim)"
                                 "Induct_on" ("no rule-induction for " ^ Name)
                | try (th :: rest) =
                    Tactic.HO_MATCH_MP_TAC th g
                    handle Feedback.HOL_ERR _ => try rest
          in try ths end
      end
end;

fun (q by tac) =
    Tactical.THEN1 (Q.SUBGOAL_THEN q Tactic.STRIP_ASSUME_TAC,
                    Tactical.THEN (tac, Tactical.NO_TAC));
infix 8 suffices_by;
fun (q suffices_by tac) =
    Tactical.THEN1 (Tactical.Q_TAC Tactic.SUFF_TAC q,
                    Tactical.THEN (tac, Tactical.NO_TAC));

fun readFile path =
    let val is = TextIO.openIn path
        val s = TextIO.inputAll is
    in TextIO.closeIn is; s end;
fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;

(* the rebind shim, injected after the header chunk (whose opens re-spill
   the image's old bindings into the global env). srw_tac is the lowercase
   alias `val rw = srw_tac[]` (script line 43) wants. *)
val () = writeFile ("/tmp/asweep_rebind.sml",
  String.concatWith "\n" [
    "val new_definition = boolLib.new_definition;",
    "val save_thm = boolLib.save_thm;",
    "val SRW_TAC = BasicProvers.SRW_TAC;",
    "val srw_tac = BasicProvers.SRW_TAC;",
    "val RW_TAC = BasicProvers.RW_TAC;",
    "val rw_tac = BasicProvers.rw_tac;",
    "val simp = BasicProvers.simp;",
    "val Cases_on = BasicProvers.Cases_on;",
    "val Induct_on = BasicProvers.Induct_on;",
    "val PROVE_TAC = BasicProvers.PROVE_TAC;",
    "val ASM_SIMP_TAC = BasicProvers.ASM_SIMP_TAC;",
    "val FULL_SIMP_TAC = BasicProvers.FULL_SIMP_TAC;",
    "val asm_simp_tac = BasicProvers.ASM_SIMP_TAC;",
    "val full_simp_tac = BasicProvers.FULL_SIMP_TAC;",
    "val fs = BasicProvers.FULL_SIMP_TAC (BasicProvers.srw_ss());",
    "val SPOSE_NOT_THEN = BasicProvers.SPOSE_NOT_THEN;",
    ""]);
(* restore prim_rec's cut TC block (LESS_ALT etc.) — relationTheory's TC/RTC
   machinery makes the upstream proofs runnable now; arithmeticScript
   references these unqualified. *)
val () = (PolyML.use ((HOL ^ "/../../crates/polyml-bin/tests/hol4_support")
                      ^ "/arith_frag_tc_block.sml");
          pr "TC_BLOCK_LOADED\n")
         handle e => pr ("TC_BLOCK_FAIL :: " ^ exnMessage e ^ "\n");

val lines =
    String.fields (fn c => c = #"\n")
                  (readFile (HOL ^ "/src/num/theories/arithmeticScript.sml"));

fun isBoundary l =
    String.isPrefix "Theorem " l orelse String.isPrefix "Definition " l
    orelse String.isPrefix "Inductive " l orelse String.isPrefix "val " l
    orelse String.isPrefix "Overload" l orelse String.isPrefix "local" l
    orelse String.isPrefix "fun " l;
fun chunkName l =
    (let val tok = List.nth (String.tokens (fn c => c = #" ") l, 1)
     in hd (String.fields (fn c => c = #":" orelse c = #"[" orelse c = #"=") tok) end
     handle _ => hd (String.tokens (fn c => c = #" ") l))
    handle _ => "?";

val ok = ref 0 and bad = ref 0;
(* Known simp-loop hangs (GC churn at ~2% retained). The MIN/MAX section is
   loop-prone wholesale -> prefix skips. *)
val skip : string list = ["expbase_le_mono", "expbase_lt_mono"];
val skipPrefixes : string list = ["MIN_", "MAX_"];
fun skipped name =
    List.exists (fn s => s = name) skip orelse
    List.exists (fn p => String.isPrefix p name) skipPrefixes;

(* re-runnable (pass 2 on the exported image): chunks whose name is already
   saved are skipped; the header's new_theory is neutralized when the
   current theory is already "arithmetic" (re-running it would WIPE the
   previously banked segment). *)
fun replaceAll (s, old, new) =
    let val (pre, suf) = Substring.position old (Substring.full s)
    in if Substring.size suf = 0 then s
       else Substring.string pre ^ new
            ^ replaceAll (Substring.string (Substring.triml (size old) suf), old, new)
    end;
fun alreadySaved name =
    List.exists (fn (n, _) => n = name)
                (Theory.current_theorems () @ Theory.current_definitions ()
                 @ Theory.current_axioms ());

(* periodic snapshot: hangs killed by timeout were eating the END-only
   export three runs straight; snapshot every 40 banked chunks. *)
val sinceSnap = ref 0;
fun maybeSnap () =
    (sinceSnap := !sinceSnap + 1;
     if !sinceSnap >= 40 then
       (sinceSnap := 0;
        PolyML.export ("/tmp/hol4_arithmetic_snap", PolyML.rootFunction);
        pr "SNAP_EXPORTED\n")
     else ());

(* per-chunk SOURCE patches. MOD_exists/MOD_DIV_exist bind variables named
   MOD/DIV — upstream's parser tolerates binder-shadowing of grammar infixes,
   ours raises "No rule for [MOD]". Alpha-rename (statements stay
   alpha-equivalent; new_specification names its constants explicitly).
   THE keystone: the whole DIVISION layer (~50 MOD_*/DIV_* theorems)
   cascades from these two. *)
val chunkPatches =
  [("MOD_exists",
    [("?MOD.", "?MODf."), ("MOD k n", "MODf k n")]),
   ("MOD_DIV_exist",
    [("?MOD DIV.", "?MODf DIVf."), ("DIV k n", "DIVf k n"),
     ("MOD k n", "MODf k n"),
     ("MOD:num->num->num", "MODf:num->num->num")]),
   (* pass-1's set_fixity chunks are baked into the image grammar, so the
      prefix-style definitions can't reparse — write them infix (same defs). *)
   ("DIV_def", [("DIV m n =", "m DIV n =")]),
   ("MOD_def", [("MOD m n =", "m MOD n =")]),
   (* markerLib stub lacks RM_ALL_ABBREVS_TAC; leftover Abbrev assumptions
      are benign here. Root of the whole MODEQ_* family (numSimps' MOD_ss). *)
   ("MODEQ_NONZERO_MODEQUALITY",
    [("markerLib.RM_ALL_ABBREVS_TAC", "Tactical.ALL_TAC")])];

(* verified hand-splices (plain SML, fleet-engineered) override their chunk. *)
val SPLICEDIR = HOL ^ "/../../crates/polyml-bin/tests/hol4_support/arith_splices";
fun spliceFile name = SPLICEDIR ^ "/" ^ name ^ ".sml";
fun hasSplice name =
    (let val is = TextIO.openIn (spliceFile name) in TextIO.closeIn is; true end)
    handle _ => false;

fun runChunk (name, chunkLines) =
  if skipped name
  then pr ("CHUNK_SKIP " ^ name ^ "\n")
  else if name <> "HEADER" andalso alreadySaved name
       (* [local] chunks must ALWAYS re-run: they are session val-bindings
          consumed by later proofs, and names collide (two `lemma[local]`s
          here) — skipping leaves `lemma` bound to the WRONG theorem
          (MOD_UNIQUE's "No resolvents" root). *)
       andalso not (String.isSubstring "[local]"
                      (case chunkLines of l :: _ => l | [] => ""))
  then (ok := !ok + 1; pr ("CHUNK_HAVE " ^ name ^ "\n"))
  else if hasSplice name
  then ((PolyML.use (spliceFile name);
         ok := !ok + 1; pr ("CHUNK_SPLICED " ^ name ^ "\n"); maybeSnap ())
        handle e =>
          (bad := !bad + 1;
           pr ("CHUNK_FAIL " ^ name ^ " (splice) :: " ^
               (case e of Fail m => m | _ => exnMessage e) ^ "\n")))
  else
    let val () = pr ("CHUNK_TRY  " ^ name ^ "\n")
        val src0 = String.concatWith "\n" chunkLines
        val src =
            case List.find (fn (n, _) => n = name) chunkPatches of
                NONE => src0
              | SOME (_, ps) =>
                  List.foldl (fn ((old, new), t) => replaceAll (t, old, new)) src0 ps
        val () = writeFile ("/tmp/asweep_src.sml", src)
        val filtered0 = HOLSource.inputFile {quietOpen = false, print = fn _ => ()}
                                            "/tmp/asweep_src.sml"
        val filtered =
            if name = "HEADER" andalso Theory.current_theory () = "arithmetic"
            then replaceAll (filtered0,
                             "Theory.new_theory \"arithmetic\"", "()")
            else filtered0
        val () = writeFile ("/tmp/asweep_chunk.sml", filtered)
    in
      (PolyML.use "/tmp/asweep_chunk.sml";
       ok := !ok + 1; pr ("CHUNK_OK   " ^ name ^ "\n"); maybeSnap ())
      handle e =>
        (bad := !bad + 1;
         pr ("CHUNK_FAIL " ^ name ^ " :: " ^
             (case e of Fail m => m | _ => exnMessage e) ^ "\n"))
    end;

(* chunk the whole file; chunk 0 = header (Theory/Ancestors/Libs + prelude).
   inLocal: column-0 local..end blocks (e.g. DIV_UNIQUE's `local val (eq,ls)
   = ... in Theorem ... end`) must NOT be split at Theorem boundaries — the
   in-scope local bindings are lost (the v1 sweep failed the whole DIV
   family this way; same fix as numeral_sweep). *)
val inLocal = ref false;
fun go (cur, curName, acc) [] = List.rev ((curName, List.rev cur) :: acc)
  | go (cur, curName, acc) (l :: t) =
      if String.isPrefix "local" l andalso not (!inLocal) then
        (* a column-0 local STARTS its own chunk (v2 appended it to the
           previous chunk, where an alreadySaved name silently skipped the
           whole block). LOCALBLOCK is never a saved name -> always re-runs;
           store_thm overwriting already-saved members is safe. *)
        (inLocal := true;
         if null cur then go (l :: cur, curName, acc) t
         else go ([l], "LOCALBLOCK", (curName, List.rev cur) :: acc) t)
      else
        (if String.isPrefix "end" l then inLocal := false else ();
         if isBoundary l andalso not (null cur) andalso not (!inLocal)
         then go ([l], chunkName l, (curName, List.rev cur) :: acc) t
         else go (l :: cur, curName, acc) t);
val chunks =
    case lines of
        [] => []
      | l0 :: t => go ([l0], "HEADER", []) t;
val () = pr ("CHUNKS " ^ Int.toString (length chunks) ^ "\n");

val () =
    case chunks of
        [] => ()
      | hd0 :: rest =>
          (runChunk hd0;
           (PolyML.use "/tmp/asweep_rebind.sml"; pr "REBIND_OK\n")
             handle e => pr ("REBIND_FAIL :: " ^ exnMessage e ^ "\n");
           List.app runChunk rest);

val () = pr ("SWEEP_SUMMARY ok=" ^ Int.toString (!ok) ^ " fail=" ^
             Int.toString (!bad) ^ "\n");

(* synthesize arithmeticTheory; smoke; export. *)
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
val () = pr ("ARITHMETICTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () =
    let val os = TextIO.openOut "/tmp/arithmeticTheory_gen.sml"
    in TextIO.output (os, "structure arithmeticTheory = struct\n");
       app (fn (n, _) =>
               TextIO.output (os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
           (!btbl);
       TextIO.output (os, "end;\n"); TextIO.closeOut os
    end;
val () = (PolyML.use "/tmp/arithmeticTheory_gen.sml"; pr "STRUCT_OK\n")
         handle e => pr ("STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

val smoke = ref true;
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "arithmetic-current" (Theory.current_theory () = "arithmetic");
val () = need "num_CASES"    ((ignore (bt "num_CASES");    true) handle _ => false);
val () = need "ADD_CLAUSES"  ((ignore (bt "ADD_CLAUSES");  true) handle _ => false);
val () = need "MULT_CLAUSES" ((ignore (bt "MULT_CLAUSES"); true) handle _ => false);
val () = pr (if !smoke then "ARITH_SMOKE_PASS\n" else "ARITH_SMOKE_FAIL\n");
val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_arithmetic\n";
       PolyML.export ("/tmp/hol4_arithmetic", PolyML.rootFunction);
       pr "ARITHMETIC_SWEEP_DONE\n")
    else pr "ARITHMETIC_EXPORT_SKIPPED\n";
