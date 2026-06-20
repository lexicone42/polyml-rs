(* ============================================================================
   SEAT 3 — FOLLOW-UP DRAFT for steps (c) and (d).
   Appended AFTER /tmp/fs_descent_seat3.sml (which banks steps a,b + helpers).
   This file is a DRAFT (not yet validated by a real run). It contains:
     - le_mult_lcancel  : 0<c ==> le (c*X)(c*Y) ==> le X Y   [cheap]
     - rle_m            : the r<=m part of step (c)           [cheap]
     - (the r=m exclusion + step d are sketched in comments; the genuinely
        expensive / fiddly remainder)
   ============================================================================ *)
val () = out "SEAT3_CD_DRAFT_BEGIN\n";

(* le_mult_lcancel : lt 0 c ==> le (mult c X)(mult c Y) ==> le X Y *)
val le_mult_lcancel_GR =
  let
    val cF = Free("c_lmc", natT); val xF = Free("X_lmc", natT); val yF = Free("Y_lmc", natT)
    val hPos = Thm.assume (ctermGR (jT (lt ZeroC cF)))
    val hLe  = Thm.assume (ctermGR (jT (le (mult cF xF)(mult cF yF))))
    val goalC = le xF yF
    val tot = le_total_d (xF, yF)
    (* case le X Y : done *)
    val caseXY =
      let val h = Thm.assume (ctermGR (jT (le xF yF)))
      in Thm.implies_intr (ctermGR (jT (le xF yF))) h end
    (* case le Y X : X = Y + d ; show d = 0 -> X = Y -> le X Y *)
    val caseYX =
      let
        val hYX = Thm.assume (ctermGR (jT (le yF xF)))
        val leAbs = Abs("d", natT, oeq xF (add yF (Bound 0)))
        fun body d (hd:thm) =     (* hd : oeq X (add Y d) *)
          let
            (* c*X = c*(Y+d) = c*Y + c*d *)
            val cx1 = mult_cong_r_d (cF, xF, add yF d) hd       (* c*X = c*(Y+d) *)
            val ld  = leftdistrib_g (cF, yF, d)                  (* c*(Y+d) = c*Y + c*d *)
            val cxE = oeqTrans_r2 (cx1, ld)                      (* c*X = c*Y + c*d *)
            (* from hLe : Ex w. c*Y = c*X + w *)
            val hwAbs = Abs("w", natT, oeq (mult cF yF)(add (mult cF xF)(Bound 0)))
            fun bodyW w (hw:thm) =    (* hw : c*Y = c*X + w *)
              let
                (* c*Y = (c*Y + c*d) + w  [rewrite c*X] *)
                val Pz = Term.lambda (Free("zlmc",natT)) (oeq (mult cF yF)(add (Free("zlmc",natT)) w))
                val e1 = oeq_rw_r (Pz, mult cF xF, add (mult cF yF)(mult cF d)) cxE hw
                         (* c*Y = (c*Y + c*d) + w *)
                (* (c*Y + c*d) + w = c*Y + (c*d + w)  [assoc] *)
                val e2 = oeqTrans_r2 (e1, addassoc_g (mult cF yF, mult cF d, w))
                         (* c*Y = c*Y + (c*d + w) *)
                (* c*Y + 0 = c*Y + (c*d+w)  -> cancel -> 0 = c*d+w *)
                val e3 = oeqTrans_r2 (oeqSym_r2 (add0r_d (mult cF yF)), e2)  (* (c*Y)+0 = c*Y + (c*d+w) *)
                val z0 = add_left_cancel_g (mult cF yF, ZeroC, add (mult cF d) w) e3  (* 0 = c*d + w *)
                val cdw0 = oeqSym_r2 z0                          (* c*d + w = 0 *)
                val cd0 = add_eq_zero_left_d (mult cF d, w) cdw0 (* c*d = 0 *)
                val disj = mult_eq_zero_r (cF, d) cd0            (* c=0 \/ d=0 *)
                (* c=0 contra lt 0 c *)
                val cZc =
                  let val hcz = Thm.assume (ctermGR (jT (oeq cF ZeroC)))
                      val Psub = Term.lambda (Free("zlmc2",natT)) (lt ZeroC (Free("zlmc2",natT)))
                      val lt00 = oeq_rw_r (Psub, cF, ZeroC) hcz hPos
                      val fls = lt_irrefl_r ZeroC lt00
                  in Thm.implies_intr (ctermGR (jT (oeq cF ZeroC))) (Thm.implies_elim (oFalse_elim_r goalC) fls) end
                val cZd =
                  let val hdz = Thm.assume (ctermGR (jT (oeq d ZeroC)))
                      val xy0 = oeqTrans_r2 (hd, add_cong_r_d (yF, d, ZeroC) hdz)  (* X = Y+0 *)
                      val xy  = oeqTrans_r2 (xy0, add0r_d yF)                       (* X = Y *)
                      (* le X Y : X = Y so le X Y witness 0 : Y = X + 0 *)
                      val yx  = oeqSym_r2 xy                                        (* Y = X *)
                      val yx0 = oeqTrans_r2 (yx, oeqSym_r2 (add0r_d xF))           (* Y = X + 0 *)
                      val leXY = le_intro_d (xF, yF, ZeroC) yx0
                  in Thm.implies_intr (ctermGR (jT (oeq d ZeroC))) leXY end
              in disjE_r (oeq cF ZeroC, oeq d ZeroC, goalC) disj cZc cZd end
          in exE_r (hwAbs, goalC) hLe "w_lmc" natT bodyW end
        val r = exE_r (leAbs, goalC) hYX "d_lmc" natT body
      in Thm.implies_intr (ctermGR (jT (le yF xF))) r end
  in Thm.implies_intr (ctermGR (jT (lt ZeroC cF)))
       (Thm.implies_intr (ctermGR (jT (le (mult cF xF)(mult cF yF))))
         (disjE_r (le xF yF, le yF xF, goalC) tot caseXY caseYX)) end;
val le_mult_lcancel_vGR = varify le_mult_lcancel_GR;
fun le_mult_lcancel_r (cT,xT,yT) hpos hle =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("c_lmc",0), ctermGR cT),(("X_lmc",0), ctermGR xT),(("Y_lmc",0), ctermGR yT)] le_mult_lcancel_vGR)) hpos) hle;
val () = out ("le_mult_lcancel_GR hyps="^Int.toString(length(Thm.hyps_of le_mult_lcancel_GR))^"\n");
val () = out "SEAT3_CD_LE_MULT_LCANCEL_OK\n";

(* ============================================================================
   step (c) r<=m  : from each le (2x') m and sumLHS = m*r derive le r m.
     sq_le on each (2x')<=m : le ((2x')^2)(m^2).  add_le_mono x3 :
        le ((2a')^2+(2b')^2+(2c')^2+(2d')^2)(m^2+m^2+m^2+m^2).
     proveIdentityG : (2a')^2+(2b')^2+(2c')^2+(2d')^2 = 4*sumLHS = 4*(m*r) = (m*(4*r))  [assoc/comm]
                      m^2+m^2+m^2+m^2 = m*(4*m).
     rewrite both -> le (m*(4*r))(m*(4*m)) ; le_mult_lcancel m -> le (4*r)(4*m)
       = le (m'*r)(m'*m) with m'=4 ; lt 0 4 ; le_mult_lcancel 4 -> le r m.
   The r=m EXCLUSION (forces all 2x'=m, m even) is the documented fiddly piece;
   sketched below, NOT completed in this draft.
   ============================================================================ *)
val () = out "SEAT3_CD_DRAFT_END (r<=m + le_mult_lcancel ready; r=m exclusion + step d NOT done here)\n";
