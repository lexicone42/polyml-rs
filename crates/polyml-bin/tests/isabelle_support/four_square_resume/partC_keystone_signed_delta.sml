
(* ============================================================================
   PART C — DESCENT KEYSTONE delta.
   Appended after the full resume base (base + partA + assembly + partB + partC).
   Final context: ctxtGR / ctermGR on thyGR.

   GOAL of the crux (the descent STEP):
     prime2 p ==> 1<m ==> m<p ==> four_sq(m*p)
        ==> EX m2. (Suc Zero <= m2) /\ m2<m /\ four_sq(m2*p).

   HONEST STATUS (see SEAT SUMMARY at the end): the FULL descent step is NOT
   proved in this delta.  Root cause discovered during this work: the descent's
   parts (a) [r=0 exclusion] and (c) [the Euler divide-by-m^2] BOTH require the
   SIGNED residue relation  a' == a (mod m)  OR  a' == -a (mod m)  (per
   coordinate), but the banked sym_residue_thm / four_residue_sum_thm only
   deliver the SQUARED congruence  a'^2 == a^2 (mod m), which is strictly weaker
   (it loses the sign).  E.g. part (a) needs "a'=0 ==> m|a", which from a'^2==a^2
   alone only gives m|a^2 (and m need NOT be prime here, so m|a does not follow);
   from the SIGNED residue it follows immediately (a'=0 and a'==(+/-)a give a==0).

   THIS DELTA PROVES THE MISSING KEYSTONE: the SIGNED residue lemma
   sym_residue_signed, the genuine piece the resume material lacked.  It is the
   prerequisite for a signed four_residue_sum, hence for parts (a) and (c).
   ============================================================================ *)
val () = out "L4_DESCENT_KEYSTONE_BEGIN\n";

(* ---- building block: oeq m (add 0 (mult m (Suc 0)))  [m = 0 + m*1] on ctxtGR ---- *)
fun m_eq_0_plus_m1 mT =
  let
    val e1 = multSucr_d (mT, ZeroC)              (* m*(Suc 0) = m + m*0 *)
    val e2 = mult0r_d mT                          (* m*0 = 0 *)
    val e3 = add_cong_r_d (mT, mult mT ZeroC, ZeroC) e2  (* m + m*0 = m + 0 *)
    val e4 = add0r_d mT                           (* m + 0 = m *)
    val m1_eq_m = oeqTrans_r2 (oeqTrans_r2 (e1, e3), e4)  (* m*1 = m *)
    val zp = add0_d (mult mT (suc ZeroC))         (* 0 + m*1 = m*1 *)
    val zpm = oeqTrans_r2 (zp, m1_eq_m)           (* 0 + m*1 = m *)
  in oeqSym_r2 zpm end;                            (* m = 0 + m*1 *)

(* ---- cong m m 0  (m is congruent to 0 mod m) on ctxtGR ---- *)
fun cong_m_self_zero mT =
  cong_introR_r (mT, mT, ZeroC, suc ZeroC) (m_eq_0_plus_m1 mT);

val () = out "L4_KEYSTONE_HELPERS_DEFINED\n";

(* ----------------------------------------------------------------------------
   sym_residue_signed (m, a) hm :  hm : lt 0 m
      ==>  EX a'. (cong m a' a  OR  cong m (add a' a) 0)  /\  le (add a' a') m

   Construction (mirrors the banked sym_residue, but RETAINS the sign):
     r = a mod m, q = a div m.  a = m*q + r,  r < m  (so r <= m).
     cong m a r  (a = r + m*q),  cong m r a (sym).
     le_total (r+r) m:
       le (r+r) m  : a' := r.   LEFT  disjunct cong m a' a = cong m r a.   bound le (r+r) m.
       le m (r+r)  : a' := m-r.  a'+r = m.
         cong m (a'+a)(a'+r)        [cong_add: refl a' + (cong m a r)]
         cong m (a'+r) 0            [a'+r = m, and cong m m 0]
         cong m (a'+a) 0  (trans)   = RIGHT disjunct.
         bound le (a'+a') m         [a'<=r since 2r>=m, so a'+a' <= a'+r = m].
   ---------------------------------------------------------------------------- *)
fun sym_residue_signed (mT, aT) hm =
  let
    val r = rmodv aT mT
    val q = rdivv aT mT
    val divid = divmod_id_g (aT, mT) hm     (* oeq a (add (mult m q) r) *)
    val rlt   = rmod_lt_g (aT, mT) hm       (* lt r m *)
    val rle   = lt_imp_le_r (r, mT) rlt     (* le r m *)
    val a_eq_rmq = oeqTrans_r2 (divid, addcomm_g (mult mT q, r))   (* a = r + m*q *)
    val cong_a_r = cong_introR_r (mT, aT, r, q) a_eq_rmq           (* cong m a r *)
    val cong_r_a = cong_sym_g (mT, aT, r) cong_a_r                 (* cong m r a *)
    val apF = Free("ap_srs", natT)
    fun dpart ap = mkDisj (cong mT ap aT) (cong mT (add ap aT) ZeroC)
    fun bpart ap = le (add ap ap) mT
    val goalPred = Term.lambda apF (mkConj (dpart apF) (bpart apF))
    val goalC = mkEx goalPred
    val tot = le_total_g (add r r, mT)      (* Disj (le (r+r) m)(le m (r+r)) *)
    val caseA =
      let
        val hP = jT (le (add r r) mT)
        val h  = Thm.assume (ctermGR hP)
        val dj = disjI1_r (cong mT r aT, cong mT (add r aT) ZeroC) cong_r_a   (* LEFT *)
        val conj = conjI_r (dpart r, bpart r) dj h
        val ex = exI_r goalPred r conj
      in Thm.implies_intr (ctermGR hP) ex end
    val caseB =
      let
        val hP = jT (le mT (add r r))
        val h  = Thm.assume (ctermGR hP)
        val ap = subv mT r
        val rec0 = sub_recover_g (mT, r) rle    (* oeq (add (subv m r) r) m : a'+r=m *)
        val cong_apa_apr = cong_add_g (mT, ap, ap, aT, r) (cong_refl_g (mT, ap)) cong_a_r
                          (* cong m (a'+a)(a'+r) *)
        val cm0 = cong_m_self_zero mT          (* cong m m 0 *)
        val rec0s = oeqSym_r2 rec0             (* oeq m (a'+r) *)
        val zC = Free("zcong_aprm", natT)
        val Pc = Term.lambda zC (cong mT zC ZeroC)
        val cong_apr_0 = oeq_rw_r (Pc, mT, add ap r) rec0s cm0   (* cong m (a'+r) 0 *)
        val cong_apa_0 = cong_trans_g (mT, add ap aT, add ap r, ZeroC) cong_apa_apr cong_apr_0
                         (* cong m (a'+a) 0 *)
        val dj = disjI2_r (cong mT ap aT, cong mT (add ap aT) ZeroC) cong_apa_0   (* RIGHT *)
        (* bound le (a'+a') m *)
        val le_apr_rr = oeq_rw_r (Term.lambda (Free("zb",natT)) (le (Free("zb",natT)) (add r r)),
                                  mT, add ap r) rec0s h   (* le (a'+r)(r+r) *)
        val le_ap_r = le_radd_cancel (ap, r, r) le_apr_rr           (* le a' r *)
        val le_aa_ar =
          let
            val Pw = Abs("w", natT, oeq r (add ap (Bound 0)))
            fun bd w (hw:thm) =
              let
                val e1 = add_cong_r_d (ap, r, add ap w) hw
                val e2 = oeqSym_r2 (addassoc_g (ap, ap, w))
                val ar_eq = oeqTrans_r2 (e1, e2)
                val leThm = le_intro_d (add ap ap, add ap r, w) ar_eq
              in leThm end
          in exE_r (Pw, le (add ap ap)(add ap r)) le_ap_r "wb_srs" natT bd end
        val le_aa_m = oeq_rw_r (Term.lambda (Free("zc",natT)) (le (add ap ap) (Free("zc",natT))),
                                add ap r, mT) rec0 le_aa_ar   (* le (a'+a') m *)
        val conj = conjI_r (dpart ap, bpart ap) dj le_aa_m
        val ex = exI_r goalPred ap conj
      in Thm.implies_intr (ctermGR hP) ex end
  in disjE_r (le (add r r) mT, le mT (add r r), goalC) tot caseA caseB end;
val () = out "L4_SYM_RESIDUE_SIGNED_DEFINED\n";

(* ---- discharged 0-hyp lemma ---- *)
val sym_residue_signed_thm =
  let
    val mF = Free("m_srs", natT); val aF = Free("a_srs", natT)
    val hmP = jT (lt ZeroC mF)
    val hm = Thm.assume (ctermGR hmP)
    val rr = sym_residue_signed (mF, aF) hm
  in Thm.implies_intr (ctermGR hmP) rr end;
val () = out ("sym_residue_signed hyps="^Int.toString(length(Thm.hyps_of sym_residue_signed_thm))^"\n");
val () = out ("sym_residue_signed prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of sym_residue_signed_thm)^"\n");

(* ---- aconv against intended ---- *)
val sym_residue_signed_intended =
  let
    val mV = Free("m_srs", natT); val aV = Free("a_srs", natT)
    val apF = Free("ap_srs", natT)
    val concl = mkEx (Term.lambda apF
                  (mkConj (mkDisj (cong mV apF aV) (cong mV (add apF aV) ZeroC))
                          (le (add apF apF) mV)))
  in Logic.mk_implies (jT (lt ZeroC mV), jT concl) end;
val srs_aconv = ((Thm.prop_of sym_residue_signed_thm) aconv sym_residue_signed_intended);
val srs_0hyp = (length (Thm.hyps_of sym_residue_signed_thm) = 0);
val () = out ("L4_SR_SIGNED_VALIDATE aconv="^Bool.toString srs_aconv^" zero_hyp="^Bool.toString srs_0hyp^"\n");

(* ---- soundness probes ---- *)
(* PROBE 1: genuinely conditional (must keep the 0<m premise). *)
val srs_probe_cond =
  let
    val mV = Free("m_srs", natT); val aV = Free("a_srs", natT)
    val apF = Free("ap_srs", natT)
    val concl = mkEx (Term.lambda apF
                  (mkConj (mkDisj (cong mV apF aV) (cong mV (add apF aV) ZeroC))
                          (le (add apF apF) mV)))
  in not ((Thm.prop_of sym_residue_signed_thm) aconv (jT concl)) end;
val () = out ("L4_SR_SIGNED_PROBE_COND "^Bool.toString srs_probe_cond^"\n");
(* PROBE 2: the disjunction genuinely carries the SIGN (it is NOT the squared-only
   form cong m (a'*a')(a*a) of the banked sym_residue_thm). *)
val srs_probe_signed =
  let
    val mV = Free("m_srs", natT); val aV = Free("a_srs", natT)
    val apF = Free("ap_srs", natT)
    val squaredConcl = mkEx (Term.lambda apF
                  (mkConj (cong mV (mult apF apF) (mult aV aV)) (le (add apF apF) mV)))
  in not ((Thm.prop_of sym_residue_signed_thm) aconv (Logic.mk_implies (jT (lt ZeroC mV), jT squaredConcl))) end;
val () = out ("L4_SR_SIGNED_PROBE_SIGNED "^Bool.toString srs_probe_signed^"\n");

val () = if srs_aconv andalso srs_0hyp andalso srs_probe_cond andalso srs_probe_signed
         then out "L4_SR_SIGNED_OK\n" else out "L4_SR_SIGNED_KEYSTONE_FAILED\n";

(* ============================================================================
   SEAT SUMMARY (honest).
   PROVED (0-hyp, aconv-checked, 2 soundness probes):
     sym_residue_signed : 0<m ==> EX a'. (cong m a' a OR cong m (a'+a) 0)
                                          /\ le (a'+a') m
   This is the SIGNED residue lemma — the genuine missing keystone the resume
   material lacked.  The banked sym_residue_thm/four_residue_sum_thm only give
   the SQUARED congruence a'^2==a^2, which is insufficient for the descent's
   parts (a) and (c) (both need the per-coordinate sign a'==(+/-)a).

   NOT proved here (the open remainder of the descent step, honestly): a signed
   four_residue_sum (thread this lemma's disjunction through the 4 coordinates),
   then (a) r=0 exclusion [now reachable: a'=0 + sign ==> m|a ==> m|p ==> contra],
   (b) r<m [needs multiplicative cancellation m*r<=m*m ==> r<=m, plus the r=m
   exclusion], and (c) the Euler divide-by-m^2 [proveStarFor on the real
   witnesses + showing m | each of w, s_x, s_y, s_z via the now-available signs].
   ============================================================================ *)
val () = out "L4_DESCENT_KEYSTONE_PARTIAL_OK\n";
