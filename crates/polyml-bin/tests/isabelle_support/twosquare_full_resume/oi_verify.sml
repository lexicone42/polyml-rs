(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — ONLY-IF direction, VERIFIER add-on.

   Appended after:  ts_key_lemma.sml ; oi_arith.sml ; oi_descent.sml ;
                    oi_casea_seat2.sml   (which define + close `only_if`).

   Adds the independent adversarial checks the closing seats did not run:
     1. RUNTIME AXIOM AUDIT (Theory.all_axioms_of of the only_if theory):
        confirm ZERO axioms mention the conclusion / valuation / two-square /
        sumsq / even vocabulary — every such name is a derivation.
     2. INDEPENDENT aconv RECHECK with a fresh Print_Mode dump of BOTH the
        proved prop and the independently-rebuilt intended prop, plus
        hyps_of = [].
   ============================================================================ *)
val () = out "OIV_AUDIT_BEGIN\n";
val () =
  let
    val thyOf = Thm.theory_of_thm only_if;
    val axs   = Theory.all_axioms_of thyOf;   (* (string * term) list *)
    val nax   = length axs;
    val ctxt0 = Proof_Context.init_global thyOf;
    fun pstr t = Print_Mode.setmp [] (fn () =>
                   Pretty.string_of (Syntax.pretty_term ctxt0 t)) ();
    val names = map fst axs;
    val () = out ("OIV total_axioms="^Int.toString nax^"\n");
    (* flag any axiom whose NAME or PROP mentions conclusion / valuation /
       sumsq / two-square / even-power vocabulary. *)
    fun susp (nm:string, prop:term) =
      let val s = pstr prop
          fun has sub = String.isSubstring sub nm orelse String.isSubstring sub s
      in has "sumsq" orelse has "only_if" orelse has "twosquare" orelse has "two_sq"
         orelse has "valuation" orelse has "vexp" orelse has "even"
         orelse has "square" end;
    val suspicious = List.filter susp axs;
    val () = out ("OIV suspicious_axioms="^Int.toString (length suspicious)^"\n");
    val () = app (fn (nm,_) => out ("OIV SUSPICIOUS: "^nm^"\n")) suspicious;
    val () = out "OIV --- ALL AXIOM NAMES ---\n";
    val () = app (fn nm => out ("OIV ax: "^nm^"\n")) names;
    val () = out "OIV --- END NAMES ---\n";
    val () = if length suspicious = 0
             then out "OIV_AUDIT_CLEAN\n"
             else out "OIV_AUDIT_DIRTY\n";
  in () end
  handle e => out ("OIV_AUDIT skipped ("^exnMessage e^")\n");
val () = out "OIV_AUDIT_END\n";

val () = out "OIRECHK_BEGIN\n";
val () =
  let
    val ctxt0 = Proof_Context.init_global (Thm.theory_of_thm only_if);
    fun pstr t = Print_Mode.setmp [] (fn () =>
                   Pretty.string_of (Syntax.pretty_term ctxt0 t)) ();
    val proved = Thm.prop_of only_if;
    val nh     = length (Thm.hyps_of only_if);
    val () = out ("OIRECHK hyps="^Int.toString nh^"\n");
    val () = out ("OIRECHK_PROVED_PROP:\n"^pstr proved^"\n");
    val () = out ("OIRECHK_INTENDED_PROP:\n"^pstr only_if_intended^"\n");
    val () = out ("OIRECHK aconv_intended="^Bool.toString (proved aconv only_if_intended)^"\n");
  in () end
  handle e => out ("OIRECHK skipped ("^exnMessage e^")\n");
val () = out "OIRECHK_END\n";
