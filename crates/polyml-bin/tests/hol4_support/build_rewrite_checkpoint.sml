(* build_rewrite_checkpoint.sml — add HOL4's rewriting engine (REWRITE_TAC) on
   top of the warm tactic checkpoint and export /tmp/hol4_rewrite.
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_tactic  (basis+kernel+Theory+parser+bool+core tactic layer;
   built by build_tactic_checkpoint.sml).

   REWRITE_TAC lives in src/1/Rewrite.sig.  Rewrite.sml opens
     HolKernel boolTheory boolSyntax Drule BoundedRewrites Abbrev
   and drives the term-net via Net + Conv's REWR_CONV/HO_REWR_CONV — all already
   on /tmp/hol4_tactic EXCEPT the one absent leaf BoundedRewrites.  So the whole
   rewriting engine is just 4 files: BoundedRewrites.{sig,sml} + Rewrite.{sig,sml}.
   The default rewrite set (`implicit_rewrites`, set to `bool_rewrites` at load)
   carries 11 boolTheory clauses (REFL_CLAUSE/EQ_CLAUSES/NOT_CLAUSES/AND_CLAUSES/
   OR_CLAUSES/IMP_CLAUSES/COND_CLAUSES/FORALL_SIMP/EXISTS_SIMP/ABS_SIMP/
   EXISTS_UNIQUE_FALSE), so REWRITE_TAC [] simplifies boolean goals with no
   explicit lemmas.  Ho_Net/Ho_Rewrite (higher-order rewriting) are NOT needed
   for plain REWRITE_TAC and are deferred.

   The explode/Definition prelude carries over from the tactic build (defensive:
   Conv-style src/1 files want the SML-default char-list explode, not the
   Portable string-list explode our checkpoint leaks to the pervasive).

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_tactic \
       crates/polyml-bin/tests/hol4_support/build_rewrite_checkpoint.sml
   Produces /tmp/hol4_rewrite.  Emits: RW_LOADED n/m, IMPLICIT_SIZE n,
   RW_PROVED …, REWRITE_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_rewrite,
   REWRITE_CHECKPOINT_DONE. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
structure PP = HOLPP;
(* restore the SML-default char-list explode (our checkpoint leaked Portable's
   string-list explode to the top-level pervasive). *)
val explode = String.explode;
val implode = String.implode;
structure Definition = Theory.Definition;

fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;

pr "\nREWRITE_LOAD_START\n";
val files = [
  "src/1/BoundedRewrites.sig", "src/1/BoundedRewrites.sml",
  "src/1/Rewrite.sig",         "src/1/Rewrite.sml"
];
val nok = foldl (fn (f,a) => if U f then a+1 else a) 0 files;
pr ("RW_LOADED " ^ Int.toString nok ^ "/" ^ Int.toString (length files) ^ "\n");
val () = (pr ("IMPLICIT_SIZE "
              ^ Int.toString (length (Rewrite.dest_rewrites (Rewrite.implicit_rewrites())))
              ^ "\n"))
         handle e => pr ("IMPLICIT_SIZE_FAIL :: " ^ exnMessage e ^ "\n");

(* smoke: REWRITE_TAC [] proves boolean goals via the default rewrite set. *)
val smoke = ref true;
fun goal tag tac q =
  (let val th = Tactical.prove (Parse.Term [QUOTE q], tac)
   in pr ("RW_PROVED " ^ tag ^ " :: " ^ Parse.thm_to_string th ^ "\n") end)
  handle e => (smoke := false; pr ("RW_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
val () = goal "and-T" (Rewrite.REWRITE_TAC []) "(T /\\ p) <=> p";
val () = goal "or-T"  (Rewrite.REWRITE_TAC []) "p \\/ T";
val () = goal "dneg"  (Rewrite.REWRITE_TAC []) "~~p <=> p";
val () = goal "asm"   (Tactical.THEN (Tactic.STRIP_TAC, Rewrite.ASM_REWRITE_TAC [])) "p ==> (p /\\ T)";
val () = pr (if !smoke andalso nok = length files
             then "REWRITE_SMOKE_PASS\n" else "REWRITE_SMOKE_FAIL\n");

val () =
    if !smoke andalso nok = length files then
      (pr "EXPORTING /tmp/hol4_rewrite\n";
       PolyML.export("/tmp/hol4_rewrite", PolyML.rootFunction);
       pr "REWRITE_CHECKPOINT_DONE\n")
    else pr "REWRITE_CHECKPOINT_SKIPPED\n";
