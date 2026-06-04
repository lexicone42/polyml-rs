(* fancy_proofs.sml — non-trivial HOL4 theorems proved by real tactics on the
   warm /tmp/hol4_simp checkpoint (HOL4 kernel + bool + combin + tactics +
   REWRITE_TAC + the simplifier, all running on the polyml-rs interpreter).

   These go well beyond the p ==> p / I x = x baseline: classical logic
   (the Drinker Paradox, quantifier duality), combinatory logic (S K K = I),
   and the simplifier normalizing compound combinator terms.

   Run:  tools/sml-exp.sh --steps 40000000000 /tmp/hol4_simp \
           crates/polyml-bin/tests/hol4_support/fancy_proofs.sml
   Each line prints  =PROVED= [name] <theorem>  or  =FAIL= name: <exn>.

   Boundary notes (no boolLib/bossLib here, so no PROVE_TAC/METIS/DECIDE):
   SPEC/GEN live in Thm/Drule; SIMP_TAC with empty_ss does not auto-close x=x
   (append THEN REWRITE_TAC []). *)

infix THEN THENL THEN1 ORELSE;
fun pr s = print (s ^ "\n");
fun show name th = pr ("=PROVED= [" ^ name ^ "] " ^ Parse.thm_to_string th);
fun tryit name f = (f ()) handle e => pr ("=FAIL= " ^ name ^ ": " ^ exnMessage e);
val REPEAT=Tactical.REPEAT; val GEN_TAC=Tactic.GEN_TAC; val EQ_TAC=Tactic.EQ_TAC;
val STRIP_TAC=Tactic.STRIP_TAC; val DISCH_TAC=Tactic.DISCH_TAC; val EXISTS_TAC=Tactic.EXISTS_TAC;
val CCONTR_TAC=Tactic.CCONTR_TAC; val ASM_CASES_TAC=Tactic.ASM_CASES_TAC;
val DISJ1_TAC=Tactic.DISJ1_TAC; val DISJ2_TAC=Tactic.DISJ2_TAC; val MATCH_MP_TAC=Tactic.MATCH_MP_TAC;
val ACCEPT_TAC=Tactic.ACCEPT_TAC; val FIRST_ASSUM=Tactical.FIRST_ASSUM;
val FIRST_X_ASSUM=Tactical.FIRST_X_ASSUM; val POP_ASSUM=Tactical.POP_ASSUM;
val RES_TAC=Tactic.RES_TAC; val ASSUME_TAC=Tactic.ASSUME_TAC; val X_CHOOSE_TAC=Tactic.X_CHOOSE_TAC;
val prove=Tactical.prove; val REWRITE_TAC=Rewrite.REWRITE_TAC; val ASM_REWRITE_TAC=Rewrite.ASM_REWRITE_TAC;
val REWRITE_RULE=Rewrite.REWRITE_RULE;
val SIMP_TAC=simpLib.SIMP_TAC; val empty_ss=simpLib.empty_ss; val rewrites=simpLib.rewrites;
val op ++ = simpLib.++; val T=Parse.Term;

val _ = tryit "univ_mp_dist" (fn () => show "univ_mp_dist" (prove (T [QUOTE "!P Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)"],
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])));
val _ = tryit "forall_conj" (fn () => show "forall_conj" (prove (T [QUOTE "!P Q. (!x. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)"],
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [])));
val _ = tryit "skk_eq_i" (fn () => show "skk_eq_i" (prove (T [QUOTE "S K K = I"],
  REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC [combinTheory.S_THM, combinTheory.K_THM, combinTheory.I_THM])));
val _ = tryit "comp_assoc" (fn () => let val ss=empty_ss ++ rewrites [combinTheory.o_THM] in
  show "comp_assoc" (prove (T [QUOTE "!f g h x. ((f o g) o h) x = (f o (g o h)) x"], SIMP_TAC ss [] THEN REWRITE_TAC [])) end);
val _ = tryit "simp_compound" (fn () => let val ss=empty_ss ++ rewrites [combinTheory.S_THM, combinTheory.K_THM, combinTheory.I_THM, combinTheory.o_THM] in
  show "simp_compound" (prove (T [QUOTE "!f x. (f o I) x = S K K (f x)"], SIMP_TAC ss [] THEN REWRITE_TAC [])) end);
val _ = tryit "ex_or_allnot" (fn () => show "ex_or_allnot" (prove (T [QUOTE "!P. (?x. P x) \\/ (!x. ~ P x)"],
  GEN_TAC THEN ASM_CASES_TAC (T [QUOTE "?x. (P:'a->bool) x"]) THENL [
    DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    DISJ2_TAC THEN GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (T [QUOTE "x:'a"]) THEN FIRST_ASSUM ACCEPT_TAC ])));
val _ = tryit "exists_dual" (fn () => show "exists_dual" (prove (T [QUOTE "!P. (?x. P x) <=> ~(!x. ~ P x)"],
  GEN_TAC THEN EQ_TAC THENL [ STRIP_TAC THEN STRIP_TAC THEN RES_TAC,
    DISCH_TAC THEN CCONTR_TAC THEN POP_ASSUM (fn h2 =>
      POP_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC h2 THEN EXISTS_TAC (T [QUOTE "x:'a"]) THEN FIRST_ASSUM ACCEPT_TAC) ])));
val _ = tryit "drinker" (fn () => show "drinker_paradox" (prove (T [QUOTE "?x:'a. D x ==> !y. D y"],
  ASM_CASES_TAC (T [QUOTE "!y. (D:'a->bool) y"]) THENL [
    EXISTS_TAC (T [QUOTE "@x:'a. T"]) THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    POP_ASSUM (fn notall => ASSUME_TAC (REWRITE_RULE [boolTheory.NOT_FORALL_THM] notall)) THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC (T [QUOTE "w:'a"])) THEN EXISTS_TAC (T [QUOTE "w:'a"]) THEN DISCH_TAC THEN RES_TAC ])));
val _ = pr "FANCY_PROOFS_DONE";
