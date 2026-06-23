(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — MERGE SEAT 1 assembly.

   Appended AFTER (in ONE process):
     isabelle_twosquare.sml            (monolith -> final context ctxtGR; `twosquare`)
     if_direction.sml .. if_full_direction.sml   (the if-direction deltas on ctxtGR;
                                          gives `if_direction : 0<n ==> hpBody n ==> sumsq n`
                                          [fully OBJECT form jT(Imp(lt 0 n)(Imp R L))], 0-hyp,
                                          plus term builders sumsqBody/hpBody/vpredBody/
                                          fourk3/evenBody/innerAllE/hpInnerBody and the
                                          ND toolkit mp_r/impI_r/conjI_gr_at/...)
     /tmp/flt_region.sml               (the spine binom->binom_theorem->freshman_dream->
                                          flt->apm1->key_onlyif sub-tree, RE-ROOTED onto
                                          thyGR : thyB extends thyGR ; thySub adds ONLY `sumf`
                                          and reuses the monolith's Pure.sub, so ctxtSub/
                                          ctermSub EXTENDS thyGR ; gives `key_onlyif` on ctxtSub)
     oi_arith.sml ; oi_descent.sml ; oi_casea_seat2.sml
                                       (the only-if descent on ctxtSub ; gives `only_if`
                                          on ctxtSub, the PER-PRIME EXISTENTIAL even-valuation:
                                          prime2 p ==> (Ex k.p=4k+3) ==> (0<n /\ sumsq n)
                                            ==> Ex v m. n=p^v*m /\ ~p|m /\ Ex j. v=j+j)

   THE MERGE THIS SEAT ACHIEVES:
     * key_onlyif + only_if are now PROVED on ctxtSub, which EXTENDS thyGR
       (the documented "splice the FLT/binom/key_onlyif sub-tree onto thyGR", RESUME item A).
       So the two directions live on COMPATIBLE contexts in ONE process -- the merge backbone.
     * The FULL IFF is assembled on ctxtGR MODULO the only-if half taken as an object hyp
       (if_iff form), with the second conjunct = the PROVED unconditional if_direction.

   THE ONE REMAINING GAP to the UNCONDITIONAL universal iff (RESUME item B): the only_if is
   PROVED in the PER-PRIME EXISTENTIAL even-valuation form, but the iff's hpBody needs the
   UNIVERSAL form (!e. vpred p n e ==> even e).  Bridging needs valuation UNIQUENESS
   (vpred p n e1 ==> vpred p n e2 ==> e1=e2), which needs `mult_left_cancel` (cancel a
   positive p-power) -- NOT in the monolith (only add_left_cancel is) and a real sub-development.
   ============================================================================ *)
val () = out "TSF_SEAT1_ASSEMBLY_BEGIN\n";

(* ---- (1) both directions present + on compatible contexts ---- *)
val () = out ("SEAT1 if_direction hyps="^Int.toString(length(Thm.hyps_of if_direction))^"\n");
val () = out ("SEAT1 only_if hyps="^Int.toString(length(Thm.hyps_of only_if))^"\n");
val () = out ("SEAT1 key_onlyif hyps="^Int.toString(length(Thm.hyps_of key_onlyif))^"\n");

(* if_direction's prop must cterm cleanly on ctxtSub  ==>  ctxtSub extends thyGR. *)
val ifdir_on_sub_ok =
  (let val _ = Thm.cterm_of ctxtSub (Thm.prop_of if_direction) in true end) handle _ => false;
val () = if ifdir_on_sub_ok
         then out "SEAT1_CTXT_COMPAT_OK if_direction prop is a valid cterm on ctxtSub (ctxtSub extends thyGR)\n"
         else out "SEAT1_CTXT_COMPAT_FAIL\n";

(* runtime: thyGR (thy of if_direction) IS a sub-theory of thySub (thy of only_if). *)
val merge_subthy_ok =
  (Context.subthy (Thm.theory_of_thm if_direction, Thm.theory_of_thm only_if)) handle _ => false;
val () = if merge_subthy_ok
         then out "SEAT1_SUBTHY_OK thy(if_direction) <= thy(only_if) -- only_if lives ABOVE thyGR (the splice)\n"
         else out "SEAT1_SUBTHY_FAIL only_if NOT above thyGR\n";

(* only_if (descent) is also valid as a cterm on ctxtSub (it IS on ctxtSub) -- sanity. *)
val onlyif_self_ok =
  (let val _ = Thm.cterm_of ctxtSub (Thm.prop_of only_if) in true end) handle _ => false;
val () = if onlyif_self_ok then out "SEAT1_ONLYIF_ON_SUB_OK\n" else out "SEAT1_ONLYIF_ON_SUB_FAIL\n";

(* dump the merged-context only_if statement for the record *)
val () = out ("SEAT1_ONLYIF_PROP:\n" ^ Syntax.string_of_term ctxtSub (Thm.prop_of only_if) ^ "\n");
val () = out "TSF_SEAT1_PROBE_DONE\n";

(* ---- (2) the FULL IFF on ctxtGR MODULO the existential->universal bridge ----
   This is exactly if_iff.sml's construction (the if-direction half is the PROVED
   unconditional if_direction on ctxtGR; the only-if half is the object hyp oiH), built
   on ctxtGR where mp_r / conjI_gr_at / sumsqBody / hpBody all live. *)
val () = out "TSF_SEAT1_IFF_BEGIN\n";

val twosquare_full_seat1_modulo_bridge =
  let
    val nF = Free("n_tsf", natT);
    val L  = sumsqBody nF;     (* sum of two squares *)
    val R  = hpBody nF;        (* the per-prime even-valuation RHS (universal hpBody) *)
    val hPosP = jT (lt ZeroC nF); val hPos = Thm.assume (ctermGR hPosP);
    val oiHP  = jT (mkImp L R);   val oiH  = Thm.assume (ctermGR oiHP);   (* assumed only-if (object) *)
    (* if_direction at n on ctxtGR : 0<n ==> hpBody n ==> sumsq n (all object Imps). *)
    val ifAt = beta_norm (Drule.infer_instantiate ctxtGR [(("n_if",0), ctermGR nF)] if_direction);
    val if1 = mp_r (lt ZeroC nF, mkImp (hpBody nF) (sumsqBody nF)) ifAt hPos;  (* hpBody n ==> sumsq n *)
    val ifObj = if1;   (* jT (Imp R L) *)
    val iffConj = conjI_gr_at (mkImp L R, mkImp R L) oiH ifObj;
    val body = Thm.implies_intr (ctermGR oiHP) iffConj;
    val full = Thm.implies_intr (ctermGR hPosP) body;
  in varify full end;

val () = out ("TSF_SEAT1_IFF_BUILT hyps="
              ^Int.toString(length(Thm.hyps_of twosquare_full_seat1_modulo_bridge))^"\n");

(* validation : 0-hyp + aconv intended biconditional *)
val tsf_seat1_intended =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in Logic.mk_implies (jT (lt ZeroC nV),
       Logic.mk_implies (jT (mkImp L R),
         jT (mkConj (mkImp L R) (mkImp R L)))) end;
val s1_hyps = length (Thm.hyps_of twosquare_full_seat1_modulo_bridge);
val s1_aconv = (Thm.prop_of twosquare_full_seat1_modulo_bridge) aconv tsf_seat1_intended;
val () = out ("TSF_SEAT1_IFF hyps="^Int.toString s1_hyps^" aconv="^Bool.toString s1_aconv^"\n");

(* soundness probe: second conjunct is genuinely R==>L (the if-direction), not a copy of oiH *)
val s1_probe =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
      val bogus = Logic.mk_implies (jT (lt ZeroC nV),
                    Logic.mk_implies (jT (mkImp L R),
                      jT (mkConj (mkImp L R) (mkImp L R))))
  in not ((Thm.prop_of twosquare_full_seat1_modulo_bridge) aconv bogus) end;
val () = if s1_probe then out "PROBE_OK seat1 iff second conjunct is the if-direction (R==>L)\n"
         else out "PROBE_FAIL seat1 iff second conjunct collapsed\n";
(* soundness probe 2: keeps 0<n *)
val s1_probe2 =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
      val bogus = Logic.mk_implies (jT (mkImp L R), jT (mkConj (mkImp L R) (mkImp R L)))
  in not ((Thm.prop_of twosquare_full_seat1_modulo_bridge) aconv bogus) end;
val () = if s1_probe2 then out "PROBE_OK seat1 iff keeps 0<n\n" else out "PROBE_FAIL seat1 iff dropped 0<n\n";

val () = if s1_hyps = 0 andalso s1_aconv andalso s1_probe andalso s1_probe2
         then out "TSF_SEAT1_IFF_MODULO_BRIDGE_CLOSED\n" else out "TSF_SEAT1_IFF_FAILED\n";
val () = out "TSF_SEAT1_ASSEMBLY_DONE\n";
