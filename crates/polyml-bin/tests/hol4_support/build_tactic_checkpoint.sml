(* build_tactic_checkpoint.sml — load HOL4's core tactic layer (src/1) on top of
   the warm bool-theory checkpoint, prove a goal with real tactics, and export
   /tmp/hol4_tactic.
   ---------------------------------------------------------------------------
   BASE: /tmp/hol4_bool  (basis + kernel + Theory + parser + bool theory; built
   by build_bool_checkpoint.sml, which synthesizes `structure boolTheory`).

   The minimal tactic chain (27 files incl. sigs):
     ThmAttribute, Abbrev, thmpos_dtype, Rsyntax, Psyntax, boolSyntax, Drule,
     Conv, Thm_cont, Tactical, FullUnify, resolve_then, mp_then, Tactic.
   Leaves/aliases the layer needs that aren't top-level on the checkpoint:
     - `structure Definition = Theory.Definition`  (boolSyntax uses bare Definition)
     - thin `structure DB` over DB_dtype            (boolSyntax.sig: DB.thm_src_location;
       the full DB search layer — DBSearchParser/regexpMatch — is NOT needed)
     - `val explode = String.explode` / `val implode = String.implode`:
       our checkpoint leaked Portable.explode (string list) to the top-level
       pervasive; Conv.sml's dest_path uses bare `explode` expecting char list
       (real HOL4 compiles each file with the SML-default explode).  Restore it.

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_bool \
       crates/polyml-bin/tests/hol4_support/build_tactic_checkpoint.sml
   Produces /tmp/hol4_tactic.  Emits: TAC_LOADED n/m, STUCK <path>…,
   TACTIC_PROVED …, TACTIC_SMOKE_PASS|FAIL, EXPORTING /tmp/hol4_tactic,
   TACTIC_CHECKPOINT_DONE. *)

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
structure DB = struct
  datatype thm_src_location = datatype DB_dtype.thm_src_location
  datatype class = datatype DB_dtype.class
end;

val files = [
  "src/1/ThmAttribute.sig",  "src/1/ThmAttribute.sml",
  "src/1/Abbrev.sig",        "src/1/Abbrev.sml",
  "src/1/thmpos_dtype.sml",
  "src/1/Rsyntax.sig",       "src/1/Rsyntax.sml",
  "src/1/Psyntax.sig",       "src/1/Psyntax.sml",
  "src/1/boolSyntax.sig",    "src/1/boolSyntax.sml",
  "src/1/Drule.sig",         "src/1/Drule.sml",
  "src/1/Conv.sig",          "src/1/Conv.sml",
  "src/1/Thm_cont.sig",      "src/1/Thm_cont.sml",
  "src/1/Tactical.sig",      "src/1/Tactical.sml",
  "src/1/FullUnify.sig",     "src/1/FullUnify.sml",
  "src/1/resolve_then.sig",  "src/1/resolve_then.sml",
  "src/1/mp_then.sig",       "src/1/mp_then.sml",
  "src/1/Tactic.sig",        "src/1/Tactic.sml"
];

(* fixpoint loader — retry each file across passes until convergence. *)
fun tryUse f = (PolyML.use (HOL ^ "/" ^ f); true) handle _ => false;
fun pass (rem, prog) = case rem of [] => (prog, [])
  | f :: rest => if tryUse f then let val (p,l) = pass(rest,true) in (p,l) end
                 else let val (p,l) = pass(rest,prog) in (p, f::l) end;
fun loop (rem, n) =
  if n <= 0 then rem
  else let val (_, left) = pass (rem, false)
       in if null left then [] else if length left = length rem then left
          else loop (left, n-1) end;
pr "\nTAC_FP_START\n";
val stuck = loop (files, 20);
pr ("TAC_LOADED " ^ Int.toString (length files - length stuck) ^ "/"
    ^ Int.toString (length files) ^ "\n");
List.app (fn f => pr ("STUCK " ^ f ^ "\n")) stuck;

(* smoke: prove real goals with real tactics. *)
val smoke = ref true;
fun fail tag e = (smoke := false; pr ("TACTIC_FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n"));
val () =
  (let val tm  = Parse.Term [QUOTE "p ==> p"]
       val tac = Tactical.THEN (Tactic.DISCH_TAC, Tactical.POP_ASSUM Tactic.ACCEPT_TAC)
       val th  = Tactical.prove (tm, tac)
   in if boolSyntax.is_imp (Thm.concl th) andalso null (Thm.hyp th)
      then pr "TACTIC_PROVED p==>p\n"
      else (smoke := false; pr "TACTIC_BAD p==>p\n")
   end) handle e => fail "p==>p" e;
val () =
  (let val tm  = Parse.Term [QUOTE "p /\\ q ==> q /\\ p"]
       val tac = Tactical.THEN (Tactic.STRIP_TAC,
                   Tactical.THEN (Tactic.CONJ_TAC, Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC))
       val th  = Tactical.prove (tm, tac)
   in if boolSyntax.is_imp (Thm.concl th) andalso null (Thm.hyp th)
      then pr "TACTIC_PROVED conj-comm\n"
      else (smoke := false; pr "TACTIC_BAD conj-comm\n")
   end) handle e => fail "conj-comm" e;
val () = pr (if !smoke andalso null stuck then "TACTIC_SMOKE_PASS\n" else "TACTIC_SMOKE_FAIL\n");

val () =
    if !smoke andalso null stuck then
      (pr "EXPORTING /tmp/hol4_tactic\n";
       PolyML.export("/tmp/hol4_tactic", PolyML.rootFunction);
       pr "TACTIC_CHECKPOINT_DONE\n")
    else pr "TACTIC_CHECKPOINT_SKIPPED\n";
