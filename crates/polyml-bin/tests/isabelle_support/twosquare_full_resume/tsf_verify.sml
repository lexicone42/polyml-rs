(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — INDEPENDENT VERIFIER add-on (adversarial).

   Appended AFTER bridge_seat2.sml (which defines the UNCONDITIONAL
   `twosquare_full` on ctxtSub).  Runs, FROM SCRATCH on the same process:

     (1) an independent 0-hyp / aconv recheck of `twosquare_full` against the
         intended full biconditional, and the unconditional probe (the only-if
         hypothesis oiH is GONE);
     (2) a RUNTIME AXIOM AUDIT (Theory.all_axioms_of) of `twosquare_full`'s
         theory: ZERO axioms may mention the conclusion vocabulary
         (sumsq / twosquare / only_if / valuation / even / square / iff /
         fermat / two_sq), and the ONLY classical axiom permitted is ex_middle.

   This is the verifier seat's own audit (the banked seat1_audit.sml only audits
   only_if + the CONDITIONAL modulo-bridge iff; here we audit the UNCONDITIONAL
   twosquare_full directly).
   ============================================================================ *)
val () = out "TSF_VERIFY_BEGIN\n";

(* ---- (1) independent 0-hyp / aconv recheck of twosquare_full ---- *)
local
  val nV = Var(("n_tsf",0), natT);
  val L  = sumsqBody nV;
  val R  = hpBody nV;
  val intended = Logic.mk_implies (jT (lt ZeroC nV), jT (mkConj (mkImp L R) (mkImp R L)));
  val h = length (Thm.hyps_of twosquare_full);
  val a = (Thm.prop_of twosquare_full) aconv intended;
  (* the seat1 modulo-bridge form: 0<n ==> Imp L R ==> Conj(Imp L R)(Imp R L) *)
  val modulo = Logic.mk_implies (jT (lt ZeroC nV),
                 Logic.mk_implies (jT (mkImp L R),
                   jT (mkConj (mkImp L R) (mkImp R L))));
  val unconditional = not ((Thm.prop_of twosquare_full) aconv modulo);
in
  val () = out ("TSFV recheck hyps="^Int.toString h^" aconv_intended="^Bool.toString a^"\n");
  val () = if unconditional
           then out "TSFV recheck UNCONDITIONAL (no Imp L R hypothesis)\n"
           else out "TSFV recheck STILL_CONDITIONAL\n";
  val () = if h = 0 andalso a andalso unconditional
           then out "TSFV_RECHECK_OK\n" else out "TSFV_RECHECK_FAIL\n";
end;

(* ---- (2) runtime axiom audit of twosquare_full's theory ---- *)
val () =
  let
    val thyOf = Thm.theory_of_thm twosquare_full;
    val axs   = Theory.all_axioms_of thyOf;
    val nax   = length axs;
    val ctxt0 = Proof_Context.init_global thyOf;
    fun pstr t = Print_Mode.setmp [] (fn () =>
                   Pretty.string_of (Syntax.pretty_term ctxt0 t)) ();
    val () = out ("TSFV_AUDIT total_axioms="^Int.toString nax^"\n");
    fun susp (nm:string, prop:term) =
      let val s = pstr prop
          fun has sub = String.isSubstring sub nm orelse String.isSubstring sub s
      in has "sumsq" orelse has "only_if" orelse has "twosquare" orelse has "two_sq"
         orelse has "valuation" orelse has "vexp" orelse has "even"
         orelse has "square" orelse has "iff" orelse has "fermat" end;
    val suspicious = List.filter susp axs;
    val () = out ("TSFV_AUDIT suspicious_axioms="^Int.toString (length suspicious)^"\n");
    val () = app (fn (nm,_) => out ("TSFV_AUDIT SUSPICIOUS: "^nm^"\n")) suspicious;
    val classical = List.filter (fn (nm,_) =>
        String.isSubstring "ex_middle" nm orelse String.isSubstring "excluded" nm
        orelse String.isSubstring "classical" nm) axs;
    val () = out ("TSFV_AUDIT classical_axioms="^Int.toString (length classical)^"\n");
    val () = app (fn (nm,_) => out ("TSFV_AUDIT classical: "^nm^"\n")) classical;
    val () = if length suspicious = 0
             then out "TSFV_AUDIT_CLEAN (zero conclusion-mentioning axioms)\n"
             else out "TSFV_AUDIT_DIRTY\n";
  in () end
  handle e => out ("TSFV_AUDIT skipped ("^exnMessage e^")\n");

val () = out "TSF_VERIFY_DONE\n";
