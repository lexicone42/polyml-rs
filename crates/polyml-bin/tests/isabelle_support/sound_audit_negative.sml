(* ============================================================================
   NEGATIVE TEST for the shared soundness audit (sound_audit.sml).

   Runs on the classical NT foundation (with_nt_helpers -> ex_middle is present,
   so a genuine theorem passes the classical == 1 gate). It then synthesises the
   two failure modes the audit is meant to catch and confirms each one FIRES
   `SOUND_AUDIT_FAIL` (not `SOUND_AUDIT_OK`):

     neg_clean    : a genuine 0-hyp NT theorem (prime_divisor_exists)     -> OK
     neg_smuggled : a fabricated axiom OUTSIDE the conservative allowlist -> FAIL
     neg_oracle   : a Skip_Proof (oracle-tainted) theorem                 -> FAIL

   This proves the allowlist / oracle checks actually reject violations rather
   than merely printing OK on clean input.
   ============================================================================ *)

(* the genuine, conservative theorem the nt_helpers foundation already proved *)
val neg_clean_thm = prime_divisor_exists;
val neg_thy = Thm.theory_of_thm prime_divisor_exists;

(* --- failure mode 1 : a fabricated axiom whose name is NOT on the allowlist.
   `smuggled_false_lemma` is not a recognised conservative name, so the axiom
   allowlist check must reject it. --- *)
val ((_, neg_smuggled_thm), _) =
  Thm.add_axiom_global (Binding.name "smuggled_false_lemma", Free ("P", propT)) neg_thy;

(* --- failure mode 2 : an oracle-tainted theorem via Skip_Proof.  Set
   Proofterm.proofs := 0 first (as the heavy proofs do) to prove the oracle
   name is STILL recorded and detected in that regime. --- *)
val () = Proofterm.proofs := 0;
val neg_oracle_thm =
  Skip_Proof.make_thm neg_thy (Thm.term_of (Thm.global_cterm_of neg_thy (Free ("Q", propT))));

val () = TextIO.output (TextIO.stdOut, "NEG_SETUP_DONE\n");
