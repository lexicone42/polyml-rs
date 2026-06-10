(* build_prim_rec_checkpoint.sml — Stage 1 of the Datatype roadmap: build the
   REAL prim_recTheory on /tmp/hol4_num and export /tmp/hol4_prim_rec.

   (Supersedes the 2026-06-04 WIP that was blocked on UNIQUE_SKOLEM_THM — the
   num_arith_trophy.sml HO_REWR_CONV technique, 2026-06-05, unblocked it; see
   the fragments below. Old version in git history.)

   prim_recScript.sml proves the primitive recursion theorem (num_Axiom) from
   Peano's axioms. Two parts don't fit this chain and are surgically replaced
   (everything else is upstream text, run verbatim through the quote filter):

     * the TC block (TC_LESS_0..LESS_ALT) + LESS_LEMMA1's TC proof need
       relationTheory -> CUT the block, splice the TC-free LESS_LEMMA1 from
       num_arith_trophy.sml         (prim_rec_frag_less_lemma1.sml);
     * SIMP_REC's specification uses SIMP_RULE bool_ss [UNIQUE_SKOLEM_THM]
       (absent from our synthesized boolTheory) -> splice the hand proof +
       HO_REWR_CONV pipeline         (prim_rec_frag_simp_rec.sml);
     * `local open BasicProvers in end` in the header (BasicProvers needs
       srw_ss; Stage 2-3) -> dropped;
     * TypeBase.export + the wellfounded/WF/measure tail (relationTheory.WF)
       -> truncated (the WF tail returns at Stage 2-3 with relationTheory).

   The filtered text is split at decl boundaries into parts so each chunk
   loads (and fails) independently:
     part1 [start, TC_LESS_0) ; part2 [LESS_SUC_REFL, LESS_LEMMA1) ; FRAG1 ;
     part3 [LESS_LEMMA2, SIMP_REC-spec) ; FRAG2 ; part4 [LESS_SUC_SUC,
     TypeBase.export).

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh --steps 400000000000 \
       /tmp/hol4_num crates/polyml-bin/tests/hol4_support/build_prim_rec_checkpoint.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val REPO = HOL ^ "/../..";
val FRAGDIR = REPO ^ "/crates/polyml-bin/tests/hol4_support";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
infix THEN THENL THEN1 ORELSE;

pr "\nPRIM_REC_BUILD_START\n";

(* new_theory on a non-empty base implicitly exports unless interactive. *)
val () = Globals.interactive := true;

(* KEYSTONE (as in build_num): re-register the bool ancestor axioms so
   uptodate_thm accepts theorems inheriting bool-axiom nonces. *)
val () =
    app (fn (nm, ax) =>
            (Theory.register_replayed_axiom ax; pr ("REG_AX " ^ nm ^ "\n"))
            handle e => pr ("REG_AX_FAIL " ^ nm ^ " :: " ^ exnMessage e ^ "\n"))
        [("BOOL_CASES_AX", boolTheory.BOOL_CASES_AX),
         ("ETA_AX",        boolTheory.ETA_AX),
         ("SELECT_AX",     boolTheory.SELECT_AX),
         ("INFINITY_AX",   boolTheory.INFINITY_AX)];

(* ---------------------------------------------------------------------------
   Filter + split. All anchors are starts of top-level decls (split-safe).
   --------------------------------------------------------------------------- *)
val raw = HOLSource.inputFile {quietOpen=false, print=fn _ => ()}
              (HOL ^ "/src/num/theories/prim_recScript.sml");

fun splitAt (s, anchor) =
    let val (pre, suf) = Substring.position anchor (Substring.full s)
    in if Substring.size suf = 0
       then (pr ("ANCHOR_MISSING [" ^ anchor ^ "]\n"); (s, ""))
       else (Substring.string pre, Substring.string suf)
    end;

val (p1_raw, rest)  = splitAt (raw,  "val TC_LESS_0");
val (_, rest)       = splitAt (rest, "val LESS_SUC_REFL");
val (p2, rest)      = splitAt (rest, "val LESS_LEMMA1");
val (_, rest)       = splitAt (rest, "val LESS_LEMMA2");
val (p3, rest)      = splitAt (rest, "val SIMP_REC = new_specification");
val (_, rest)       = splitAt (rest, "val LESS_SUC_SUC");
val (p4a, rest)     = splitAt (rest, "val SIMP_REC_THM");
val (_, rest)       = splitAt (rest, "val PRIM_REC_FUN");
val (p4b, _)        = splitAt (rest, "val _ = TypeBase.export");

(* header patch: drop `local open BasicProvers in end ;` (absent until
   Stage 2-3 gives it a real srw_ss). *)
val p1 =
    let val (h_pre, h_suf) = splitAt (p1_raw, "local open")
        val (_, h_rest)    = splitAt (h_suf, "in end ;")
    in if h_rest = "" then p1_raw
       else h_pre ^ String.extract (h_rest, size "in end ;", NONE)
    end;

fun writeFile (path, s) =
    let val os = TextIO.openOut path in TextIO.output (os, s); TextIO.closeOut os end;
val () = writeFile ("/tmp/prim_part1.sml", p1);
val () = writeFile ("/tmp/prim_part2.sml", p2);
val () = writeFile ("/tmp/prim_part3.sml", p3);
val () = writeFile ("/tmp/prim_part4a.sml", p4a);
val () = writeFile ("/tmp/prim_part4b.sml", p4b);

(* widen the live (build_num-synthesized) boolLib with save_thm_at — the
   quote-filter expands `Theorem name = expr` to boolLib.save_thm_at, which
   the narrow boolLib lacks (same fix as build_combin, minimal form: the
   prim_rec Theorem-= forms carry no attributes). *)
structure boolLib = struct
  open boolLib
  val save_thm = Theory.save_thm
  fun save_thm_at _ x = Theory.save_thm x   (* loc arg: thm_src_location *)
end;

val parts_ok = ref true;
(* NB not named `U`: part1's `open HolKernel` rebinds U (Lib's list union)
   in the global env, shadowing any later uses. *)
fun usePart tag f =
    (PolyML.use f; pr ("USED_OK   " ^ tag ^ "\n"))
    handle e => (parts_ok := false;
                 pr ("USE_FAIL  " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));

val () = usePart "part1(header..LESS_MONO_EQ)"    "/tmp/prim_part1.sml";
val () = usePart "part2(LESS_SUC_REFL..LESS_SUC)" "/tmp/prim_part2.sml";
val () = usePart "frag1(LESS_LEMMA1 TC-free)"     (FRAGDIR ^ "/prim_rec_frag_less_lemma1.sml");
val () = usePart "part3(LESS_LEMMA2..UNIQUE_RESULT)" "/tmp/prim_part3.sml";
val () = usePart "frag2(UNIQUE_SKOLEM+SIMP_REC)"  (FRAGDIR ^ "/prim_rec_frag_simp_rec.sml");
val () = usePart "part4a(LESS_SUC_SUC)"           "/tmp/prim_part4a.sml";
val () = usePart "frag3(SIMP_REC_THM trophy)"     (FRAGDIR ^ "/prim_rec_frag_simp_rec_thm.sml");
val () = usePart "part4b(PRIM_REC..num_case)"     "/tmp/prim_part4b.sml";

val () = pr ("PRIM_REC current=" ^ Theory.current_theory () ^ "\n");

(* ---------------------------------------------------------------------------
   synthesize structure prim_recTheory from the live segment (build_num pattern).
   --------------------------------------------------------------------------- *)
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
val () = pr ("PRIMRECTHEORY_NAMES " ^ Int.toString (length (!btbl)) ^ "\n");
val () =
    let val os = TextIO.openOut "/tmp/prim_recTheory_gen.sml"
    in TextIO.output (os, "structure prim_recTheory = struct\n");
       app (fn (n, _) =>
               TextIO.output (os, "  val " ^ n ^ " = bt \"" ^ n ^ "\";\n"))
           (!btbl);
       TextIO.output (os, "end;\n"); TextIO.closeOut os
    end;
val () = (PolyML.use "/tmp/prim_recTheory_gen.sml"; pr "PRIMRECTHEORY_STRUCT_LOADED\n")
         handle e => pr ("PRIMRECTHEORY_STRUCT_FAIL :: " ^ exnMessage e ^ "\n");

(* ---------------------------------------------------------------------------
   smoke then export.
   --------------------------------------------------------------------------- *)
val smoke = ref (!parts_ok);
fun need tag b = if b then pr ("OK " ^ tag ^ "\n")
                 else (smoke := false; pr ("MISSING " ^ tag ^ "\n"));
val () = need "prim_rec-current" (Theory.current_theory () = "prim_rec");
val () = need "num_Axiom"    ((ignore (bt "num_Axiom");    true) handle _ => false);
val () = need "SIMP_REC_THM" ((ignore (bt "SIMP_REC_THM"); true) handle _ => false);
val () = need "PRIM_REC_THM" ((ignore (bt "PRIM_REC_THM"); true) handle _ => false);
val () = need "LESS_THM"     ((ignore (bt "LESS_THM");     true) handle _ => false);
val () = need "PRE"          ((ignore (bt "PRE");          true) handle _ => false);
val () = need "LESS_LEMMA1"  ((ignore (bt "LESS_LEMMA1");  true) handle _ => false);
val () = need "hyp-free"
              ((List.all (fn n => null (Thm.hyp (bt n)))
                         ["num_Axiom", "LESS_THM", "SIMP_REC_THM"])
               handle _ => false);
val () = (pr ("num_Axiom = " ^ Parse.thm_to_string (bt "num_Axiom") ^ "\n"))
         handle e => pr ("num_Axiom_PRINT_FAIL :: " ^ exnMessage e ^ "\n");
val () = pr (if !smoke then "PRIM_REC_SMOKE_PASS\n" else "PRIM_REC_SMOKE_FAIL\n");

val () =
    if !smoke then
      (pr "EXPORTING /tmp/hol4_prim_rec\n";
       PolyML.export ("/tmp/hol4_prim_rec", PolyML.rootFunction);
       pr "PRIM_REC_CHECKPOINT_DONE\n")
    else pr "PRIM_REC_CHECKPOINT_SKIPPED\n";
