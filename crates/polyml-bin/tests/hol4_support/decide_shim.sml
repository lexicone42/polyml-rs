(* DECIDE / DECIDE_TAC: numLib's arithmetic decision procedure, absent from our
   checkpoints (numLib isn't fully loaded). numpairScript uses DECIDE 10x.
   numLib's def is `ARITH_PROVE tm handle _ => tautLib.TAUT_PROVE tm`; our
   ARITH_PROVE = EQT_ELIM o Arith.ARITH_CONV (verified working on /tmp/hol4_defn).
   DECIDE_TAC = MATCH_ACCEPT of DECIDE on the goal (undischarging arith asms),
   simplified to: prove the goal (with asms discharged) via DECIDE. *)
local open boolLib in
val ARITH_PROVE = fn tm => Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun DECIDE tm =
    ARITH_PROVE tm
    handle HolKernel.HOL_ERR _ =>
      (tautLib.TAUT_PROVE tm
       handle HolKernel.HOL_ERR _ =>
         raise HolKernel.mk_HOL_ERR "decide_shim" "DECIDE" "");
(* discharge the (arithmetic) assumptions into the goal, then DECIDE it *)
fun DECIDE_TAC (g as (asl, w)) =
    (MAP_EVERY UNDISCH_TAC asl THEN
     CONV_TAC (fn tm => Drule.EQT_INTRO (DECIDE tm))) g
    handle _ =>
    (CONV_TAC (fn tm => Drule.EQT_INTRO (DECIDE tm))) g;
end;
val () = print "DECIDE_SHIM_OK\n";
