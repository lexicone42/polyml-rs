(* prove_induction.sml — the TROPHY: the first genuine induction proof on the
   polyml-rs Rust interpreter.  Built on /tmp/hol4_num (kernel+Theory+parser+
   bool+combin+numTheory).  We load src/1/Prim_rec (generic structural-induction
   support — it does NOT depend on prim_recTheory; INDUCT_THEN takes the
   induction theorem as an argument), define
        INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC
   and prove a goal that GENUINELY needs induction over the naturals:
        !n. (n = 0) \/ (?m. n = SUC m)
   (the "every nat is zero or a successor" cases theorem — not provable by
   rewriting alone; the base case is n=0, the step assumes the property for n
   and discharges it for SUC n).

   Usage (cwd = vendor/polyml, or set HOL4_DIR):
     HOL4_DIR=<repo>/vendor/hol4 tools/sml-exp.sh /tmp/hol4_num \
       crates/polyml-bin/tests/hol4_support/prove_induction.sml                *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val HOL = case OS.Process.getEnv "HOL4_DIR" of
              SOME s => if s <> "" then s else "../hol4"
            | NONE => "../hol4";
val explode = String.explode; val implode = String.implode;
structure Definition = Theory.Definition;
infix THEN THENL THEN1 ORELSE;

fun U f =
    let val p = HOL ^ "/" ^ f
    in (PolyML.use p; pr ("USED_OK   " ^ f ^ "\n"); true)
       handle e => (pr ("USE_FAIL  " ^ f ^ " :: " ^ exnMessage e ^ "\n"); false)
    end;
fun Uabs p =
    (PolyML.use p; pr ("USED_OK   " ^ p ^ "\n"); true)
    handle e => (pr ("USE_FAIL  " ^ p ^ " :: " ^ exnMessage e ^ "\n"); false);

pr "\nPROVE_INDUCTION_START\n";
val () = pr ("BASE current_theory=" ^ Theory.current_theory() ^ "\n");
val () = (pr ("numTheory.INDUCTION = " ^ Parse.thm_to_string numTheory.INDUCTION ^ "\n"))
         handle e => pr ("INDUCTION_MISSING :: " ^ exnMessage e ^ "\n");

(* Patch src/1/Prim_rec.sml: replace the grammarDB{bool} guard (NONE on our
   checkpoint) with the live Parse.Type/Parse.Term, exactly like
   build_simp_checkpoint.sml's patchPrimrec. *)
fun patchPrimrec () =
  let val raw = TextIO.inputAll (TextIO.openIn (HOL ^ "/src/1/Prim_rec.sml"))
      fun rs (s, f, r) =
          let val (pre,suf) = Substring.position f (Substring.full s)
          in if Substring.isEmpty suf then s
             else Substring.string pre ^ r
                  ^ Substring.string (Substring.triml (size f) suf) end
      val p1 = rs(raw,
            "val bool_grammars = Option.valOf $ grammarDB {thyname=\"bool\"}",
            "val bool_grammars = ()")
      val p2 = rs(p1,
            "val (Type,Term) = parse_from_grammars bool_grammars",
            "val (Type,Term) = (Parse.Type, Parse.Term)")
      val os = TextIO.openOut "/tmp/Prim_rec_patched.sml"
  in TextIO.output(os, p2); TextIO.closeOut os end;

val () = patchPrimrec();
val _ = U "src/1/Prim_rec.sig";
val primrec_ok = Uabs "/tmp/Prim_rec_patched.sml";
val () = pr ("PRIMREC_LOADED " ^ (if primrec_ok then "yes" else "no") ^ "\n");

val () = (ignore Prim_rec.INDUCT_THEN; pr "HAVE Prim_rec.INDUCT_THEN\n")
         handle e => pr ("MISS Prim_rec.INDUCT_THEN :: " ^ exnMessage e ^ "\n");

(* INDUCT_TAC over the naturals — exactly prim_recScript.sml:73's definition. *)
val INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC;

val npass = ref 0;
fun report tag thm =
    (pr (tag ^ " = " ^ Parse.thm_to_string thm ^ "\n");
     if null (Thm.hyp thm) then (npass := !npass + 1; pr (tag ^ "_PASS\n"))
     else pr (tag ^ "_FAIL_HYPS\n"));

(* ---- TROPHY 1: cases theorem — genuine induction over num. ---------------
   |- !n. (n = 0) \/ (?m. n = SUC m)
   base n=0 reduces to (0=0)\/...; step picks witness n for SUC n.          *)
val cases_thm =
    Tactical.prove
      (Parse.Term [QUOTE "!n. (n = 0) \\/ (?m. n = SUC m)"],
       INDUCT_TAC THENL
         [ Rewrite.REWRITE_TAC [],
           Tactic.DISJ2_TAC THEN Tactic.EXISTS_TAC (Parse.Term [QUOTE "n:num"])
             THEN Rewrite.REWRITE_TAC [] ]);
val () = report "TROPHY_CASES" cases_thm;

(* ---- TROPHY 2: SUC_ID — |- !n. ~(SUC n = n), the canonical arithmetic
   induction (prim_recScript.sml:293).  The step case uses the inductive
   hypothesis (ASM_REWRITE) after INV_SUC_EQ collapses SUC m = SUC n.
   We derive INV_SUC_EQ by forward proof from numTheory.INV_SUC, exactly as
   prim_recScript.sml:82 does.                                              *)
val INV_SUC_EQ =
    let open Drule Thm
    in GENL [Parse.Term [QUOTE "m:num"], Parse.Term [QUOTE "n:num"]]
            (IMP_ANTISYM_RULE
               (SPEC_ALL numTheory.INV_SUC)
               (DISCH (Parse.Term [QUOTE "m:num = n"])
                      (AP_TERM (Parse.Term [QUOTE "SUC"])
                               (ASSUME (Parse.Term [QUOTE "m:num = n"])))))
    end;
val () = pr ("INV_SUC_EQ = " ^ Parse.thm_to_string INV_SUC_EQ ^ "\n");

val suc_id_thm =
    Tactical.prove
      (Parse.Term [QUOTE "!n. ~(SUC n = n)"],
       INDUCT_TAC THEN
         Rewrite.ASM_REWRITE_TAC [numTheory.NOT_SUC, INV_SUC_EQ]);
val () = report "TROPHY_SUC_ID" suc_id_thm;

val () = pr ("TROPHIES_PASSED " ^ Int.toString (!npass) ^ "/2\n");
val () = if !npass = 2 then pr "INDUCTION_PROOF_PASS\n"
         else pr "INDUCTION_PROOF_FAIL\n";
val () = pr "PROVE_INDUCTION_DONE\n";
