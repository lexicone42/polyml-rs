(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — MERGE SEAT 1, VERIFIER AXIOM AUDIT add-on.

   Appended AFTER seat1_iff_assembly.sml (which defines `only_if` on ctxtSub and
   `twosquare_full_seat1_modulo_bridge` on ctxtGR).  Runs the independent
   adversarial axiom audit the assembly seat did not:

     RUNTIME AXIOM AUDIT (Theory.all_axioms_of) of BOTH the merged-context
     only_if theory AND the modulo-bridge-iff theory: confirm ZERO axioms
     mention the conclusion vocabulary (sumsq / twosquare / only_if /
     valuation / even / square / iff), and that the only classical axiom
     present is `ex_middle`.  Every conclusion-vocabulary name must be a
     DERIVATION, not an axiom.
   ============================================================================ *)
val () = out "SEAT1_AUDIT_BEGIN\n";

fun audit_thy label thm =
  let
    val thyOf = Thm.theory_of_thm thm;
    val axs   = Theory.all_axioms_of thyOf;     (* (string * term) list *)
    val nax   = length axs;
    val ctxt0 = Proof_Context.init_global thyOf;
    fun pstr t = Print_Mode.setmp [] (fn () =>
                   Pretty.string_of (Syntax.pretty_term ctxt0 t)) ();
    val () = out ("SEAT1_AUDIT["^label^"] total_axioms="^Int.toString nax^"\n");
    fun susp (nm:string, prop:term) =
      let val s = pstr prop
          fun has sub = String.isSubstring sub nm orelse String.isSubstring sub s
      in has "sumsq" orelse has "only_if" orelse has "twosquare" orelse has "two_sq"
         orelse has "valuation" orelse has "vexp" orelse has "even"
         orelse has "square" orelse has "iff" orelse has "fermat" end;
    val suspicious = List.filter susp axs;
    val () = out ("SEAT1_AUDIT["^label^"] suspicious_axioms="^Int.toString (length suspicious)^"\n");
    val () = app (fn (nm,_) => out ("SEAT1_AUDIT["^label^"] SUSPICIOUS: "^nm^"\n")) suspicious;
    (* classical axioms : the ONLY one permitted is ex_middle (A \/ ~A). *)
    val classical = List.filter (fn (nm,_) =>
        String.isSubstring "ex_middle" nm orelse String.isSubstring "excluded" nm
        orelse String.isSubstring "classical" nm) axs;
    val () = out ("SEAT1_AUDIT["^label^"] classical_axioms="^Int.toString (length classical)^"\n");
    val () = app (fn (nm,_) => out ("SEAT1_AUDIT["^label^"] classical: "^nm^"\n")) classical;
  in (length suspicious, length classical) end
  handle e => (out ("SEAT1_AUDIT["^label^"] skipped ("^exnMessage e^")\n"); (~1, ~1));

val (susp_oi,  cls_oi)  = audit_thy "only_if" only_if;
val (susp_iff, cls_iff) = audit_thy "modulo_bridge_iff" twosquare_full_seat1_modulo_bridge;

(* hyps recap (already emitted, re-state for the audit block) *)
val () = out ("SEAT1_AUDIT only_if hyps="^Int.toString(length(Thm.hyps_of only_if))^"\n");
val () = out ("SEAT1_AUDIT iff hyps="^Int.toString(length(Thm.hyps_of twosquare_full_seat1_modulo_bridge))^"\n");

val () =
  if susp_oi = 0 andalso susp_iff = 0
  then out "SEAT1_AUDIT_CLEAN (zero conclusion-mentioning axioms in either theory)\n"
  else out "SEAT1_AUDIT_DIRTY\n";
val () = out "SEAT1_AUDIT_END\n";
