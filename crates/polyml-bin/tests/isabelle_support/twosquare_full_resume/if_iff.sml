(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — the assembly (CONDITIONAL on the only-if half).

   The if-direction (if_direction : 0<n ==> hpBody n ==> sumsq n) is PROVED
   unconditionally on ctxtGR above.  The only-if direction
     only_if : prime2 p ==> (Ex k. p=4k+3) ==> (0<n /\ sumsq n)
                ==> (Ex v m. n=p^v*m /\ ~p|m /\ Ex j. v=j+j)
   is BANKED (CLOSED) but on the SPINE context ctxtSub, NOT ctxtGR; and to feed
   the iff it must be (a) re-spliced onto ctxtGR (the FLT/key_onlyif sub-tree,
   ~6K lines, a multi-fleet merge) and (b) upgraded from the per-prime EXISTENTIAL
   even-valuation to the UNIVERSAL form hpBody n (which needs valuation
   UNIQUENESS).  Both are scoped as the remaining piece.

   Here we assemble the FULL IFF MODULO the only-if half: taking the only-if as
   an OBJECT-implication hypothesis  oiH : Imp (sumsq n) (hpBody n),  we build
     twosquare_full_modulo_onlyif :
       0 < n ==> Imp (sumsq n) (hpBody n)
              ==> Conj (Imp (sumsq n) (hpBody n)) (Imp (hpBody n) (sumsq n))
   i.e. GIVEN the only-if half, the full biconditional sumsq n <-> hpBody n holds
   (under 0<n).  The second conjunct is the PROVED if_direction; the first is the
   assumed only-if.  This is the honest "full iff modulo one named, scoped lemma".
   ============================================================================ *)
val () = out "TSF_IFF_BEGIN\n";

val twosquare_full_modulo_onlyif =
  let
    val nF = Free("n_iff", natT);
    val L  = sumsqBody nF;     (* sum of two squares *)
    val R  = hpBody nF;        (* the per-prime even-valuation RHS *)
    val hPosP = jT (lt ZeroC nF); val hPos = Thm.assume (ctermGR hPosP);
    val oiHP  = jT (mkImp L R);   val oiH  = Thm.assume (ctermGR oiHP);   (* assumed only-if (object) *)
    (* if-direction at n : 0<n ==> hpBody n ==> sumsq n.  Object-ify R ==> L. *)
    val ifAt = beta_norm (Drule.infer_instantiate ctxtGR [(("n_if",0), ctermGR nF)] if_direction);
    val if1 = mp_r (lt ZeroC nF, mkImp (hpBody nF) (sumsqBody nF)) ifAt hPos;  (* hpBody n ==> sumsq n *)
    (* if1 : jT (Imp (hpBody n)(sumsq n)) = jT (Imp R L) *)
    val ifObj = if1;
    (* mkConj (Imp L R)(Imp R L) *)
    val iffConj = conjI_gr_at (mkImp L R, mkImp R L) oiH ifObj;
    val body = Thm.implies_intr (ctermGR oiHP) iffConj;        (* oiH ==> Conj ... *)
    val full = Thm.implies_intr (ctermGR hPosP) body;          (* 0<n ==> oiH ==> Conj ... *)
  in varify full end;

val () = out ("TSF_IFF_BUILT hyps="^Int.toString(length(Thm.hyps_of twosquare_full_modulo_onlyif))^"\n");

(* ---- validation : 0-hyp + aconv intended ---- *)
val tsf_iff_intended =
  let val nV = Var(("n_iff",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in Logic.mk_implies (jT (lt ZeroC nV),
       Logic.mk_implies (jT (mkImp L R),
         jT (mkConj (mkImp L R) (mkImp R L)))) end;
val tsfiff_hyps = length (Thm.hyps_of twosquare_full_modulo_onlyif);
val tsfiff_aconv = (Thm.prop_of twosquare_full_modulo_onlyif) aconv tsf_iff_intended;
val () = out ("TSF_IFF hyps="^Int.toString tsfiff_hyps^" aconv="^Bool.toString tsfiff_aconv^"\n");

(* soundness probe : the SECOND conjunct (the if-direction R==>L) is genuinely the
   proved if_direction (not vacuous) -- i.e. the conclusion conjunction is NOT aconv
   the trivial Conj (Imp L R)(Imp L R) (which would mean the if-direction half is
   secretly the assumed only-if).  Confirm the proved thm is NOT aconv that variant. *)
val tsfiff_probe =
  let val nV = Var(("n_iff",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
      val bogus = Logic.mk_implies (jT (lt ZeroC nV),
                    Logic.mk_implies (jT (mkImp L R),
                      jT (mkConj (mkImp L R) (mkImp L R))))   (* second conjunct = Imp L R again *)
  in not ((Thm.prop_of twosquare_full_modulo_onlyif) aconv bogus) end;
val () = if tsfiff_probe then out "PROBE_OK iff second conjunct is the if-direction (R==>L), not a copy of only-if\n"
         else out "PROBE_FAIL iff second conjunct collapsed\n";
(* soundness probe 2 : keeps 0<n *)
val tsfiff_probe2 =
  let val nV = Var(("n_iff",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
      val bogus = Logic.mk_implies (jT (mkImp L R), jT (mkConj (mkImp L R) (mkImp R L)))
  in not ((Thm.prop_of twosquare_full_modulo_onlyif) aconv bogus) end;
val () = if tsfiff_probe2 then out "PROBE_OK iff keeps 0<n\n" else out "PROBE_FAIL iff dropped 0<n\n";

val () = if tsfiff_hyps = 0 andalso tsfiff_aconv andalso tsfiff_probe andalso tsfiff_probe2
         then out "TSF_IFF_MODULO_ONLYIF_CLOSED\n" else out "TSF_IFF_FAILED\n";
val () = out "TSF_IFF_DONE\n";
