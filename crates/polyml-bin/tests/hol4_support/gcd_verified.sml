(* gcd_verified.sml — Euclid's GCD, DEFINED and PROVED CORRECT on HOL4's real
   LCF kernel running on the Rust PolyML interpreter (/tmp/hol4_datatype).

   This exercises NON-STRUCTURAL recursion end to end:
     - gcd is defined by `TotalDefn.tDefine` with a measure (`measure SND`)
       and an automatically discharged termination obligation
       (a MOD b < b, via arithmeticTheory.MOD_LESS) — there is no structural
       decreasing argument, so plain `Define` cannot do it.
     - tDefine emits the RECURSION-INDUCTION principle `gcd_ind`, which is the
       only sound way to reason about the function:
         gcd_ind = |- !P. (!a b. (b <> 0 ==> P b (a MOD b)) ==> P a b)
                          ==> !v v1. P v v1
     - Both halves of gcd's specification are proved by `HO_MATCH_MP_TAC
       gcd_ind`, threading divisibility through the Euclid step via the
       division identity a = (a DIV b)*b + (a MOD b):
         gcd_divides  : |- !a b. divides (gcd a b) a /\ divides (gcd a b) b
                        (gcd a b is a COMMON DIVISOR of a and b)
         gcd_greatest : |- !a b d. divides d a /\ divides d b
                                   ==> divides d (gcd a b)
                        (it is the GREATEST — every common divisor divides it)
       Together they fully characterise gcd as the greatest common divisor in
       the divisibility order. Both are ZERO-hypothesis theorems — genuine
       elementary number theory.

   The two proof chains (ring1 -> divides_lin -> gcd_divides; then
   divides_mult/divides_sub/mod_decompose -> divides_mod -> gcd_greatest) were
   each engineered by a 3-seat proof fleet (wf_dac9e4a5-fe2 / wf_9aa3fd1e-5a7);
   all three seats converged independently in both. This is the robust variant:
   METIS is confined to the tiny nonlinear ring identity (and divides_mult
   reuses divides_lin, so the greatest-property chain needs no METIS at all);
   the main inductions use explicit MATCH_MP_TAC/ACCEPT_TAC so they never risk
   the METIS search-explosion or the recursive-rewrite loop (see the pitfall
   notes below).

   Run: tools/sml-exp.sh /tmp/hol4_datatype \
          crates/polyml-bin/tests/hol4_support/gcd_verified.sml

   Pitfalls this proof is engineered around (all reusable in this shimmed env):
   1. `REWRITE_TAC[GCD]` LOOPS — GCD is a recursive equation, so plain
      rewriting expands the else-branch gcd forever before the if-condition
      is decided. Unfold with a CONTROLLED single step
      (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV[GCD]))) in gcd_0 / gcd_step.
   2. Feeding MULT_COMM to REWRITE_TAC/SIMP_TAC LOOPS (AC permutation, no
      loop-guard here). The nonlinear ring identity is closed by METIS over a
      SMALL lemma set [LEFT_ADD_DISTRIB, MULT_ASSOC, MULT_COMM] — fine for a
      pure-multiplication goal, a search-explosion for anything with ADD
      structure, so prove it ONCE in isolation (ring1) and plug it in.
   3. A bare variable witness parses as type 'a, not :num, and won't unify
      against the existential slot — annotate `q "b:num"`.
   4. Never close a subgoal by rewriting with a self-referential equation
      (a = a DIV b * b + a MOD b reintroduces `a` infinitely) — the three
      conjuncts of divides_lin's antecedent are already assumptions, so
      discharge them with FIRST_ASSUM ACCEPT_TAC. *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL ORELSE;
open boolLib;
fun ARITH tm = Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun ARITH_TAC g = Tactic.CONV_TAC (Drule.EQT_INTRO o ARITH) g;

(* === DEFINE: Euclid's gcd by well-founded (non-structural) recursion === *)
val GCD = (let val (th,_) = TotalDefn.tDefine "gcd"
             [QUOTE "gcd a b = if b = 0 then a else gcd b (a MOD b)"]
             (Tactical.THEN (TotalDefn.WF_REL_TAC [QUOTE "measure SND"],
                Tactical.THEN (Rewrite.REWRITE_TAC [prim_recTheory.measure_thm, pairTheory.FST, pairTheory.SND],
                  Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC,
                    Tactical.THEN (Tactic.MATCH_MP_TAC arithmeticTheory.MOD_LESS,
                      Tactical.THEN (Tactical.FIRST_X_ASSUM Tactic.MP_TAC, ARITH_TAC)))))) in th end);
(* the recursion-induction principle tDefine generated alongside gcd *)
val gcd_ind = #2 (valOf (List.find (fn (n,_) => n = "gcd_ind")
                  (Theory.current_theorems () @ Theory.current_definitions ())));
val DIV = TotalDefn.Define [QUOTE "divides d n = ?k. n = d * k"];
val () = pr "GCD_SETUP_OK\n";

(* === PROVE: gcd is a common divisor of both its arguments === *)
open arithmeticTheory;
val q = fn s => Parse.Term [QUOTE s];

(* nat ring identity: q*(d*k1) + d*k2 = d*(q*k1+k2).  Small METIS lemma set (no loop). *)
val ring1 = Tactical.prove(
  q "!d q k1 k2. q * (d * k1) + d * k2 = d * (q * k1 + k2)",
  metisLib.METIS_TAC[LEFT_ADD_DISTRIB, MULT_ASSOC, MULT_COMM]);
val () = pr "OK ring1\n";

(* divisibility combines through the division identity. *)
val divides_lin = Tactical.prove(
  q "!d a b q r. divides d b /\\ divides d r /\\ (a = q * b + r) ==> divides d a",
  Rewrite.REWRITE_TAC[DIV] THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.EXISTS_TAC (q "q * k + k'") THEN
  Rewrite.ASM_REWRITE_TAC[] THEN
  Rewrite.REWRITE_TAC[ring1]);
val () = pr "OK divides_lin\n";

val divides_refl = Tactical.prove(
  q "!a. divides a a",
  Rewrite.REWRITE_TAC[DIV] THEN Tactic.GEN_TAC THEN
  Tactic.EXISTS_TAC (q "1") THEN Rewrite.REWRITE_TAC[MULT_CLAUSES]);
val () = pr "OK divides_refl\n";

val divides_zero = Tactical.prove(
  q "!a. divides a 0",
  Rewrite.REWRITE_TAC[DIV] THEN Tactic.GEN_TAC THEN
  Tactic.EXISTS_TAC (q "0") THEN Rewrite.REWRITE_TAC[MULT_CLAUSES]);
val () = pr "OK divides_zero\n";

val nz_lt = Tactical.prove(
  q "!b. b <> 0 ==> 0 < b",
  Tactic.GEN_TAC THEN Tactic.STRIP_TAC THEN
  Tactical.FIRST_X_ASSUM Tactic.MP_TAC THEN ARITH_TAC);
val () = pr "OK nz_lt\n";

(* the Euclid division identity, instantiated:  b<>0 ==> a = (a DIV b)*b + a MOD b *)
val div_id = Tactical.prove(
  q "!a b. b <> 0 ==> (a = a DIV b * b + a MOD b)",
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.MP_TAC (Drule.MATCH_MP nz_lt (Thm.ASSUME (q "b <> 0"))) THEN
  Tactic.STRIP_TAC THEN
  Tactic.MP_TAC (Drule.MATCH_MP DIVISION (Thm.ASSUME (q "0 < b"))) THEN
  Tactic.DISCH_TAC THEN
  Tactical.FIRST_X_ASSUM (fn th => Tactic.MP_TAC (Q.SPEC [QUOTE "a"] th)) THEN
  Tactic.STRIP_TAC THEN Rewrite.ASM_REWRITE_TAC[]);
val () = pr "OK div_id\n";

(* unfold gcd, controlling the recursive equation so REWRITE doesn't loop *)
val gcd_0 = Tactical.prove(
  q "!a. gcd a 0 = a",
  Tactic.GEN_TAC THEN
  Tactical.CONV_TAC (Conv.LHS_CONV (Rewrite.ONCE_REWRITE_CONV[GCD])) THEN
  Rewrite.REWRITE_TAC[]);
val () = pr "OK gcd_0\n";

val gcd_step = Tactical.prove(
  q "!a b. b <> 0 ==> (gcd a b = gcd b (a MOD b))",
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactical.CONV_TAC (Conv.LHS_CONV (Rewrite.ONCE_REWRITE_CONV[GCD])) THEN
  Rewrite.ASM_REWRITE_TAC[]);
val () = pr "OK gcd_step\n";

(* ====================== MAIN ====================== *)
val gcd_divides = Tactical.prove(
  q "!a b. divides (gcd a b) a /\\ divides (gcd a b) b",
  Tactic.HO_MATCH_MP_TAC gcd_ind THEN
  Tactical.REPEAT Tactic.GEN_TAC THEN
  Tactic.STRIP_TAC THEN
  Tactic.ASM_CASES_TAC (q "b = 0") THENL
  [ (* ---- base: b = 0 ---- *)
    Rewrite.ASM_REWRITE_TAC[gcd_0] THEN
    Tactic.CONJ_TAC THENL
    [ Rewrite.REWRITE_TAC[divides_refl],
      Rewrite.REWRITE_TAC[divides_zero] ],
    (* ---- step: b <> 0 ---- *)
    Rewrite.REWRITE_TAC[Drule.MATCH_MP gcd_step (Thm.ASSUME (q "b <> 0"))] THEN
    Tactical.FIRST_X_ASSUM (fn ih =>
        Tactic.STRIP_ASSUME_TAC (Drule.MATCH_MP ih (Thm.ASSUME (q "b <> 0")))) THEN
    Tactic.MP_TAC (Drule.MATCH_MP (Q.SPECL [[QUOTE "a"], [QUOTE "b"]] div_id)
                                  (Thm.ASSUME (q "b <> 0"))) THEN
    Tactic.STRIP_TAC THEN
    Tactic.CONJ_TAC THENL
    [ (* divides (gcd b (a MOD b)) a *)
      Tactic.MATCH_MP_TAC divides_lin THEN
      Tactic.EXISTS_TAC (q "b:num") THEN
      Tactic.EXISTS_TAC (q "a DIV b") THEN
      Tactic.EXISTS_TAC (q "a MOD b") THEN
      Tactical.REPEAT Tactic.CONJ_TAC THEN
      Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
      (* divides (gcd b (a MOD b)) b *)
      Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC ] ]);
val () = pr "OK gcd_divides\n";
val () = pr (Parse.thm_to_string gcd_divides ^ "\n");
val _ = Theory.save_thm("gcd_divides", gcd_divides);
val () = pr "SAVED gcd_divides\n";

(* ===================================================================== *)
(* === gcd_greatest: the UNIVERSAL PROPERTY — every common divisor d  === *)
(* === of a,b divides gcd a b.  With gcd_divides this fully           === *)
(* === characterises gcd as the GREATEST common divisor in the        === *)
(* === divisibility order.  (2nd 3-seat fleet: wf_9aa3fd1e-5a7,        === *)
(* === all 3 converged.)                                              === *)
(* ===================================================================== *)

(* d | b  ==>  d | q*b.   Reuse divides_lin (q*b = q*b + 0) — no new ring
   identity, no METIS, so zero loop risk. *)
val divides_mult = Tactical.prove(
  q "!d b q. divides d b ==> divides d (q * b)",
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.MATCH_MP_TAC divides_lin THEN
  Tactic.EXISTS_TAC (q "b:num") THEN
  Tactic.EXISTS_TAC (q "q:num") THEN
  Tactic.EXISTS_TAC (q "0") THEN
  Tactical.REPEAT Tactic.CONJ_TAC THENL
  [ Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
    Rewrite.REWRITE_TAC[divides_zero],
    Rewrite.REWRITE_TAC[ADD_CLAUSES] ]);
val () = pr "OK divides_mult\n";

(* d | m  /\  d | n  ==>  d | (m - n).  Truncated nat subtraction;
   LEFT_SUB_DISTRIB distributes UNCONDITIONALLY (no n<=m needed). *)
val divides_sub = Tactical.prove(
  q "!d m n. divides d m /\\ divides d n ==> divides d (m - n)",
  Rewrite.REWRITE_TAC[DIV] THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.EXISTS_TAC (q "k - k'") THEN
  Rewrite.ASM_REWRITE_TAC[] THEN
  Rewrite.REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]);
val () = pr "OK divides_sub\n";

(* b<>0 ==> a MOD b = a - (a DIV b * b).  Linear in a, a MOD b with
   (a DIV b * b) opaque: from div_id (a = adb*b + amodb) and x=y+z ==> z=x-y. *)
val mod_decompose = Tactical.prove(
  q "!a b. b <> 0 ==> (a MOD b = a - a DIV b * b)",
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.MP_TAC (Drule.MATCH_MP (Q.SPECL [[QUOTE "a"], [QUOTE "b"]] div_id)
                                (Thm.ASSUME (q "b <> 0"))) THEN
  ARITH_TAC);
val () = pr "OK mod_decompose\n";

(* b<>0 /\ d|a /\ d|b ==> d | (a MOD b). *)
val divides_mod = Tactical.prove(
  q "!d a b. b <> 0 ==> divides d a ==> divides d b ==> divides d (a MOD b)",
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[Drule.MATCH_MP (Q.SPECL [[QUOTE "a"], [QUOTE "b"]] mod_decompose)
                                     (Thm.ASSUME (q "b <> 0"))] THEN
  Tactic.MATCH_MP_TAC divides_sub THEN
  Tactic.CONJ_TAC THENL
  [ Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
    Tactic.MATCH_MP_TAC divides_mult THEN
    Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC ]);
val () = pr "OK divides_mod\n";

(* ====================== MAIN: gcd_greatest ====================== *)
val gcd_greatest = Tactical.prove(
  q "!a b d. divides d a /\\ divides d b ==> divides d (gcd a b)",
  Tactic.HO_MATCH_MP_TAC gcd_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactic.ASM_CASES_TAC (q "b = 0") THENL
  [ (* ---- base: b = 0 ---- *)
    Rewrite.ASM_REWRITE_TAC[gcd_0] THEN
    Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
    (* ---- step: b <> 0 ---- *)
    Rewrite.REWRITE_TAC[Drule.MATCH_MP gcd_step (Thm.ASSUME (q "b <> 0"))] THEN
    Tactical.FIRST_X_ASSUM (fn ih =>
        Tactic.MATCH_MP_TAC (Drule.MATCH_MP ih (Thm.ASSUME (q "b <> 0")))) THEN
    Tactic.CONJ_TAC THENL
    [ (* divides d b *)
      Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
      (* divides d (a MOD b) *)
      Tactic.MATCH_MP_TAC (Drule.MATCH_MP
          (Drule.MATCH_MP (Q.SPECL [[QUOTE "d"], [QUOTE "a"], [QUOTE "b"]] divides_mod)
                          (Thm.ASSUME (q "b <> 0")))
          (Thm.ASSUME (q "divides d a"))) THEN
      Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC ] ]);
val () = pr "OK gcd_greatest\n";
val () = pr (Parse.thm_to_string gcd_greatest ^ "\n");
val _ = Theory.save_thm("gcd_greatest", gcd_greatest);
val () = pr "SAVED gcd_greatest\n";
val () = pr "ALL_DONE\n";
