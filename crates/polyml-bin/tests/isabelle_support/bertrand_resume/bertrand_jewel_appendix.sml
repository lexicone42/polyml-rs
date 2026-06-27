(* ============================================================================
   BERTRAND JEWEL — the FINALE.  Appended AFTER
     bertrand_f7_full.sml + bertrand_w1_appendix.sml (exit stripped)
     + w1_crude_appendix.sml + w1_pow_poly_appendix.sml.
   Final context: ctxtBL/ctermBL/thyBL.  All of crude_tail, pow_bound, poly_ineq,
   seb_reduce, seb_tail_reduce, bertrand_large_given_seb, seb_hyp_prop are live.

   STAGES (each gated 0-hyp + aconv) :
     (S35)  seb35           : le 631 n ==> lt n 648 ==> SEB_HYP n.   [SEB35_OK]
     (SFT)  seb_full_tail   : !!n. le 631 n ==> SEB_HYP n.          [SEB_FULL_TAIL_OK]
     (BL)   bertrand_large631 : le 631 n ==> Ex prime in (n,2n].    [BERTRAND_LARGE631_OK]
     (MAIN) bertrand_given_chain : [bertrand_chain] ==> bertrand.   [BERTRAND_GIVEN_CHAIN_OK]

   SEB_HYP n := !!s. le (s*s)(2n) ==> lt 2n ((Suc s)^2)
                  ==> lt ((2n+1)*(2n)^(Suc s)) (pow 4 (rdiv n 3))     (= seb_hyp_prop n)

   COVERAGE : for n>=631, s=floor_sqrt(2n)>=35.  s=35 iff n in [613,647];
   s>=36 iff n>=648.  So n in [631,647] -> s=35 (seb35) ; n>=648 -> s>=36 (crude_tail).
   n<631 -> bertrand_chain.
   ============================================================================ *)
val () = (Proofterm.proofs := 0);
val () = out "BERTRAND_JEWEL_BEGIN\n";

(* numerals + small helpers *)
val cJ1   = mkNum 1; val cJ2 = twoC; val cJ3 = mkNum 3; val cJ11 = mkNum 11;
val cJ16  = mkNum 16; val cJ35 = mkNum 35; val cJ36 = mkNum 36; val cJ37 = mkNum 37;
val cJ81  = mkNum 81; val cJ128 = mkNum 128;
val cJ209 = mkNum 209; val cJ210 = mkNum 210; val cJ407 = mkNum 407;
val cJ627 = mkNum 627; val cJ629 = mkNum 629; val cJ630 = mkNum 630; val cJ631 = mkNum 631;
val cJ647 = mkNum 647; val cJ648 = mkNum 648;
val cJ1294 = mkNum 1294; val cJ1295 = mkNum 1295; val cJ1296 = mkNum 1296; val cJ2048 = mkNum 2048;
val fourCJ = suc (suc (suc (suc ZeroC)));   (* 4 = fourCBL = fourC4 *)
fun ev2 (r,t) = t;

fun lt_add_mono_lBL (Zt, Xt, Yt) hlt =
  let val base = le_add_mono_lBL (Zt, suc Xt, Yt) hlt
      val aSr = add_Sr_BL_at (Zt, Xt)
  in le_cong_lBL (add Zt (suc Xt), suc (add Zt Xt), add Zt Yt) aSr base end;

(* le 1296 (pow 2 11) numeral-light : 1296=16*81 <= 16*128=2048=2^11 *)
fun evalPow2 0 = (suc ZeroC, powZeroBL_at twoC)
  | evalPow2 kk =
      let val (rv, rth) = evalPow2 (kk-1)
          val ps = powSucBL_at (twoC, mkNum (kk-1))
          val cong = mult_cong_rBL (twoC, pow twoC (mkNum (kk-1)), rv) rth
          val (mv, mth) = mult_eval twoC rv
      in (mv, oeqtransBL OF [ps, oeqtransBL OF [cong, mth]]) end;
val (p11vJ, p11thJ) = evalPow2 11;   (* (2048, oeq (pow 2 11) 2048) *)
val le1296_pow211_J =
  let val le_81_128 = le_evalBL 81 128
      val mlm = mult_le_mono2BL (cJ16, cJ16, cJ81, cJ128) (le_reflBL_at cJ16) le_81_128
      val e1296 = ev2 (mult_eval cJ16 cJ81)
      val e2048 = ev2 (mult_eval cJ16 cJ128)
      val g0 = le_cong_lBL (mult cJ16 cJ81, cJ1296, mult cJ16 cJ128) e1296 mlm
      val g1 = le_cong_rBL (cJ1296, mult cJ16 cJ128, cJ2048) e2048 g0
  in le_cong_rBL (cJ1296, cJ2048, pow twoC cJ11) (oeqsymBL p11thJ) g1 end;
val () = out ("le1296_pow211_J 0hyp=" ^ Bool.toString (zhBL le1296_pow211_J) ^ "\n");

(* ============================================================================
   (S35)  seb35 : le 631 n ==> lt n 648 ==> SEB_HYP n.
   ============================================================================ *)
val () = out "S35_BEGIN\n";

fun seb35_body nF h631 h648 =
  let
    val twoN = add nF nF
    val DT   = rdiv nF cJ3
    (* lt 2n 1296 : from lt n 648 -> le n 647 -> le 2n 1294 -> le (Suc 2n) 1296 *)
    val le_n_647 = le_suc_inv_BL (nF, cJ647) h648
    val le_step1 = le_add_monoBL (nF, cJ647, nF) le_n_647
    val le_step2 = le_add_mono_lBL (cJ647, nF, cJ647) le_n_647
    val le_2n_647647 = le_transBL_at (add nF nF, add cJ647 nF, add cJ647 cJ647) le_step1 le_step2
    val e1294 = ev2 (add_eval cJ647 cJ647)
    val le_2n_1294 = le_cong_rBL (add nF nF, add cJ647 cJ647, cJ1294) e1294 le_2n_647647
    val le_S2n_1295 = le_suc_monoBL_at (twoN, cJ1294) le_2n_1294
    val lt_2n_1296 = le_transBL_at (suc twoN, cJ1295, cJ1296) le_S2n_1295 (le_suc_selfBL_at cJ1295)
    (* le 210 D : by contradiction (lt D 210 -> le D 209 -> n<=629 -> contra le 631 n) *)
    val lt0_3 = lt_evalBL 0 3;
    val dme_n = div_mod_eqBL (nF, cJ3) lt0_3
    val r3 = rmod nF cJ3
    val r3_le2 = le_suc_inv_BL (r3, cJ2) (rmod_ltBL (nF, cJ3) lt0_3)
    val le_210_D =
      let
        val hAss = Thm.assume (ctermBL (jT (le (suc DT) cJ210)))
        val le_D_209 = le_suc_inv_BL (DT, cJ209) hAss
        val le_3D_3209 = mult_le_monoBL (cJ3, DT, cJ209) le_D_209
        val e627 = ev2 (mult_eval cJ3 cJ209)
        val le_3D_627 = le_cong_rBL (mult cJ3 DT, mult cJ3 cJ209, cJ627) e627 le_3D_3209
        val le_sum1 = le_add_monoBL (mult cJ3 DT, cJ627, r3) le_3D_627
        val le_sum2 = le_add_mono_lBL (cJ627, r3, cJ2) r3_le2
        val e629 = ev2 (add_eval cJ627 cJ2)
        val le_sum2b = le_cong_rBL (add cJ627 r3, add cJ627 cJ2, cJ629) e629 le_sum2
        val le_n_form_629 = le_transBL_at (add (mult cJ3 DT) r3, add cJ627 r3, cJ629) le_sum1 le_sum2b
        val le_n_629 = le_cong_lBL (add (mult cJ3 DT) r3, nF, cJ629) (oeqsymBL dme_n) le_n_form_629
        val le_631_629 = le_transBL_at (cJ631, nF, cJ629) h631 le_n_629
        val lt630_630 = le_transBL_at (suc cJ630, cJ629, cJ630) le_631_629 (le_suc_selfBL_at cJ629)
        val ff = lt_irreflBL_at cJ630 OF [lt630_630]
        val negImp = impI_BL (lt DT cJ210, oFalseC) (Thm.implies_intr (ctermBL (jT (le (suc DT) cJ210))) ff)
      in nlt_leBL (DT, cJ210) negImp end;   (* le 210 D *)
    (* lt 407 (mult 2 D) : le 420 (mult 2 D) [mult_le_mono on le 210 D] ; lt 407 420 *)
    val lt407_2D =
      let val le_2_210_2D = mult_le_monoBL (cJ2, cJ210, DT) le_210_D
          val e420 = ev2 (mult_eval cJ2 cJ210)
          val le_420_2D = le_cong_lBL (mult cJ2 cJ210, mkNum 420, mult cJ2 DT) e420 le_2_210_2D
      in le_transBL_at (suc cJ407, mkNum 420, mult cJ2 DT) (lt_evalBL 407 420) le_420_2D end;
    (* inner : !!s. le (s*s) 2n ==> lt 2n ((Suc s)^2) ==> body *)
    val sB = Free("s_seb", natT)   (* MUST equal w1's seb_hyp_prop bound var *)
    val sq = mult sB sB
    val sqS = mult (suc sB)(suc sB)
    val K = sqS
    val innerBody =
      let
        val hSq  = Thm.assume (ctermBL (jT (le sq twoN)))
        val hSsq = Thm.assume (ctermBL (jT (lt twoN sqS)))
        (* le s 35 : lt (s*s) 1296 ; if le 36 s then 1296 <= s*s < 1296 contra *)
        val lt_sq_1296 = le_transBL_at (suc sq, suc twoN, cJ1296) (le_suc_monoBL_at (sq, twoN) hSq) lt_2n_1296
        val le_s_35 =
          let
            val hAss = Thm.assume (ctermBL (jT (le cJ36 sB)))   (* lt 35 s *)
            val le_3636_ss = mult_le_mono2BL (cJ36, sB, cJ36, sB) hAss hAss
            val le_1296_ss = le_cong_lBL (mult cJ36 cJ36, cJ1296, sq) (ev2 (mult_eval cJ36 cJ36)) le_3636_ss
            val lt1296_1296 = le_transBL_at (suc cJ1296, suc sq, cJ1296) (le_suc_monoBL_at (cJ1296, sq) le_1296_ss) lt_sq_1296
            val ff = lt_irreflBL_at cJ1296 OF [lt1296_1296]
            val negImp = impI_BL (lt cJ35 sB, oFalseC) (Thm.implies_intr (ctermBL (jT (le cJ36 sB))) ff)
          in nlt_leBL (cJ35, sB) negImp end;   (* le s 35 *)
        val le_Ss_36 = le_suc_monoBL_at (sB, cJ35) le_s_35      (* le (Suc s) 36 *)
        (* premise1 : le K (pow 2 11) *)
        val le_K_3636 = mult_le_mono2BL (suc sB, cJ36, suc sB, cJ36) le_Ss_36 le_Ss_36
        val le_K_1296 = le_cong_rBL (K, mult cJ36 cJ36, cJ1296) (ev2 (mult_eval cJ36 cJ36)) le_K_3636
        val le_K_pow211 = le_transBL_at (K, cJ1296, pow twoC cJ11) le_K_1296 le1296_pow211_J
        (* premise2 : lt (mult (Suc(Suc s)) 11)(mult 2 D) *)
        val le_SSs_37 = le_suc_monoBL_at (suc sB, cJ36) le_Ss_36   (* le (Suc(Suc s)) 37 *)
        val le_E11_3711 = mult_le_mono2BL (suc (suc sB), cJ37, cJ11, cJ11) le_SSs_37 (le_reflBL_at cJ11)
        val le_E11_407 = le_cong_rBL (mult (suc (suc sB)) cJ11, mult cJ37 cJ11, cJ407) (ev2 (mult_eval cJ37 cJ11)) le_E11_3711
        val lt_E11_2D = le_transBL_at (suc (mult (suc (suc sB)) cJ11), suc cJ407, mult cJ2 DT)
                          (le_suc_monoBL_at (mult (suc (suc sB)) cJ11, cJ407) le_E11_407) lt407_2D
        (* seb_reduce + seb_tail_reduce *)
        val sr = seb_reduce (sB, nF) hSsq
        val tr = seb_tail_reduce (sB, cJ11, DT) le_K_pow211 lt_E11_2D
        val LHS = mult (suc twoN)(pow twoN (suc sB))
        val g = le_transBL_at (suc LHS, suc (pow K (suc (suc sB))), pow fourCJ DT)
                  (le_suc_monoBL_at (LHS, pow K (suc (suc sB))) sr) tr
        val d2 = Thm.implies_intr (ctermBL (jT (lt twoN sqS))) g
        val d1 = Thm.implies_intr (ctermBL (jT (le sq twoN))) d2
      in d1 end
    val sebHyp = Thm.forall_intr (ctermBL sB) innerBody
    val dd2 = Thm.implies_intr (ctermBL (jT (lt nF cJ648))) sebHyp
    val dd1 = Thm.implies_intr (ctermBL (jT (le cJ631 nF))) dd2
  in dd1 end;

val seb35 =
  (let val nF = Free("n_s35", natT)
       val h631 = Thm.assume (ctermBL (jT (le cJ631 nF)))
       val h648 = Thm.assume (ctermBL (jT (lt nF cJ648)))
   in SOME (varify (seb35_body nF h631 h648)) end)
  handle e => (out ("seb35 EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val seb35_0hyp = (case seb35 of SOME th => zhBL th | NONE => false);
(* aconv : le 631 n ==> lt n 648 ==> seb_hyp_prop n *)
val seb35_aconv =
  (case seb35 of
     SOME th =>
       let val nV = Var(("n_s35",0), natT)
           val intended = Logic.mk_implies (jT (le cJ631 nV), Logic.mk_implies (jT (lt nV cJ648), seb_hyp_prop nV))
       in (Thm.prop_of th) aconv intended end
   | NONE => false);
val () = out ("seb35 0hyp=" ^ Bool.toString seb35_0hyp ^ " aconv=" ^ Bool.toString seb35_aconv ^ "\n");
val () = if seb35_0hyp andalso seb35_aconv then out "SEB35_OK\n" else out "SEB35_FAIL\n";

(* ============================================================================
   (SFT)  seb_full_tail : !!n. le 631 n ==> SEB_HYP n.
     case n < 648 -> seb35 ; case n >= 648 -> crude_tail at s (need le 36 s).
   ============================================================================ *)
val () = out "SFT_BEGIN\n";

val seb35_thm = (case seb35 of SOME th => th | NONE => raise Fail "seb35 NONE");
val crude_tail_thm = (case crude_tail of SOME th => th | NONE => raise Fail "crude_tail NONE");
val ct_vars = Term.add_vars (Thm.prop_of crude_tail_thm) [];
fun crude_tail_at (sT, nT) h36 hSq hSsq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL
        (map (fn (ix as (nm,_),_) => if nm = "s_ct2" then (ix, ctermBL sT) else (ix, ctermBL nT)) ct_vars) crude_tail_thm)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst h36) hSq) hSsq end;

(* seb35 instantiated at nT *)
fun seb35_at nT = beta_norm (Drule.infer_instantiate ctxtBL [(("n_s35",0), ctermBL nT)] seb35_thm);

(* the SEB body is an OBJECT formula (type o), so we push the n<648 / n>=648
   case-split INSIDE the meta !!s and the two floor premises ; disjE's conclusion
   C is then the object SEB body, not the meta SEB_HYP. *)
fun seb_full_tail_body nF h631 =
  let
    val twoN = add nF nF
    val DT = rdiv nF cJ3
    val sB = Free("s_seb", natT)   (* MUST equal seb_hyp_prop's bound var *)
    val sq = mult sB sB
    val sqS = mult (suc sB)(suc sB)
    (* the object SEB body formula (type o) for this s, n *)
    val sebBodyO = lt (mult (suc twoN)(pow twoN (suc sB)))(pow fourCJ DT)
    (* under the two floor hyps + h631, prove jT sebBodyO by case split *)
    val hSq  = Thm.assume (ctermBL (jT (le sq twoN)))
    val hSsq = Thm.assume (ctermBL (jT (lt twoN sqS)))
    (* CASE n<=647 : seb35 at n, forall_elim s, discharge floor hyps -> jT sebBodyO *)
    fun apply_seb35 h648 =
      let val sebN  = Thm.implies_elim (Thm.implies_elim (seb35_at nF) h631) h648   (* seb_hyp_prop n *)
          val atS   = beta_norm (Thm.forall_elim (ctermBL sB) sebN)   (* le(s*s)2n ==> lt 2n (Ss)^2 ==> jT sebBodyO *)
      in Thm.implies_elim (Thm.implies_elim atS hSq) hSsq end   (* jT sebBodyO *)
    val tot = le_totalBL (nF, cJ647)   (* Disj (le n 647)(le 647 n) *)
    val caseA =
      let val hle647 = Thm.assume (ctermBL (jT (le nF cJ647)))
          val h648 = le_suc_monoBL_at (nF, cJ647) hle647   (* le (Suc n) 648 = lt n 648 *)
      in Thm.implies_intr (ctermBL (jT (le nF cJ647))) (apply_seb35 h648) end
    val caseB =
      let
        val hle647n = Thm.assume (ctermBL (jT (le cJ647 nF)))   (* le 647 n *)
        val dj = le_eq_or_succ_leBL (cJ647, nF) hle647n   (* Disj (oeq 647 n)(le 648 n) *)
        (* B1 : oeq 647 n -> n=647 -> seb35 *)
        val caseB1 =
          let val heq = Thm.assume (ctermBL (jT (oeq cJ647 nF)))   (* oeq 647 n *)
              val le_n_647 = le_cong_rBL (nF, nF, cJ647) (oeqsymBL heq) (le_reflBL_at nF)   (* le n 647 *)
              val h648 = le_suc_monoBL_at (nF, cJ647) le_n_647
          in Thm.implies_intr (ctermBL (jT (oeq cJ647 nF))) (apply_seb35 h648) end
        (* B2 : le 648 n -> crude_tail at s (le 36 s) -> jT sebBodyO *)
        val caseB2 =
          let
            val h648n = Thm.assume (ctermBL (jT (le cJ648 nF)))   (* le 648 n *)
            val le_s1 = le_add_monoBL (cJ648, nF, cJ648) h648n        (* le (add 648 648)(add n 648) *)
            val le_s2 = le_add_mono_lBL (nF, cJ648, nF) h648n         (* le (add n 648)(add n n) *)
            val le_6486482n = le_transBL_at (add cJ648 cJ648, add nF cJ648, add nF nF) le_s1 le_s2
            val le_1296_2n = le_cong_lBL (add cJ648 cJ648, cJ1296, twoN) (ev2 (add_eval cJ648 cJ648)) le_6486482n   (* le 1296 2n *)
            (* le 36 s : if le (Suc s) 36 then K <= 1296 ; lt 2n K (hSsq) + le 1296 2n -> lt 1296 1296 *)
            val le_36_s =
              let
                val hAss = Thm.assume (ctermBL (jT (le (suc sB) cJ36)))   (* lt s 36 *)
                val le_K_3636 = mult_le_mono2BL (suc sB, cJ36, suc sB, cJ36) hAss hAss
                val le_K_1296 = le_cong_rBL (sqS, mult cJ36 cJ36, cJ1296) (ev2 (mult_eval cJ36 cJ36)) le_K_3636
                val lt_2n_1296 = le_transBL_at (suc twoN, sqS, cJ1296) hSsq le_K_1296   (* lt 2n 1296 *)
                val lt1296_1296 = le_transBL_at (suc cJ1296, suc twoN, cJ1296) (le_suc_monoBL_at (cJ1296, twoN) le_1296_2n) lt_2n_1296
                val ff = lt_irreflBL_at cJ1296 OF [lt1296_1296]
                val negImp = impI_BL (lt sB cJ36, oFalseC) (Thm.implies_intr (ctermBL (jT (le (suc sB) cJ36))) ff)
              in nlt_leBL (sB, cJ36) negImp end;   (* le 36 s *)
            val body = crude_tail_at (sB, nF) le_36_s hSq hSsq   (* jT sebBodyO *)
          in Thm.implies_intr (ctermBL (jT (le cJ648 nF))) body end
        val g = disjEBL (oeq cJ647 nF, le cJ648 nF, sebBodyO) dj caseB1 caseB2   (* jT sebBodyO *)
      in Thm.implies_intr (ctermBL (jT (le cJ647 nF))) g end
    val bodyO = disjEBL (le nF cJ647, le cJ647 nF, sebBodyO) tot caseA caseB   (* jT sebBodyO *)
    (* discharge the two floor hyps, then forall_intr s, then h631 *)
    val d2 = Thm.implies_intr (ctermBL (jT (lt twoN sqS))) bodyO
    val d1 = Thm.implies_intr (ctermBL (jT (le sq twoN))) d2          (* le(s*s)2n ==> lt 2n (Ss)^2 ==> jT sebBodyO *)
    val sebHyp = Thm.forall_intr (ctermBL sB) d1                       (* seb_hyp_prop n *)
    val dN = Thm.implies_intr (ctermBL (jT (le cJ631 nF))) sebHyp
  in dN end;

val seb_full_tail =
  (let val nF = Free("n_sft", natT)
       val h631 = Thm.assume (ctermBL (jT (le cJ631 nF)))
   in SOME (varify (seb_full_tail_body nF h631)) end)
  handle e => (out ("seb_full_tail EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val sft_0hyp = (case seb_full_tail of SOME th => zhBL th | NONE => false);
val () = (case seb_full_tail of
    SOME th => (out ("SFT_DIAG nhyps=" ^ Int.toString (length (Thm.hyps_of th))
                     ^ " nshyps=" ^ Int.toString (length (Thm.extra_shyps th)) ^ "\n");
                app (fn h => out ("  SFT_HYP : " ^ (let val s = Syntax.string_of_term ctxtBL h
                                                    in if size s > 120 then String.substring (s,0,120) ^ "...[" ^ Int.toString (size s) ^ "]" else s end) ^ "\n")) (Thm.hyps_of th))
  | NONE => ());
val sft_aconv =
  (case seb_full_tail of
     SOME th =>
       let val nV = Var(("n_sft",0), natT)
           val intended = Logic.mk_implies (jT (le cJ631 nV), seb_hyp_prop nV)
       in (Thm.prop_of th) aconv intended end
   | NONE => false);
val () = out ("seb_full_tail 0hyp=" ^ Bool.toString sft_0hyp ^ " aconv=" ^ Bool.toString sft_aconv ^ "\n");
val () = if sft_0hyp andalso sft_aconv then out "SEB_FULL_TAIL_OK\n" else out "SEB_FULL_TAIL_FAIL\n";

(* ============================================================================
   (BL)  bertrand_large631 : le 631 n ==> Ex p. prime2 p /\ lt n p /\ le p (2n).
     discharge bertrand_large_given_seb (SEB_HYP n ==> le 513 n ==> Ex ...) with
     seb_full_tail (SEB_HYP n from le 631 n) + le 513 n (513<=631<=n).
   ============================================================================ *)
val () = out "BL_BEGIN\n";

(* re-varify bertrand_large_given_seb onto ctxtBL (it was varified on V4 ; BL extends V4
   so the term is identical, but re-export to be safe for instantiation on ctxtBL). *)
val blgs_BL = Drule.zero_var_indexes (Drule.export_without_context bertrand_large_given_seb);
val blgs_vars = Term.add_vars (Thm.prop_of blgs_BL) [];
val () = out ("blgs vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) blgs_vars) ^ "\n");

val seb_full_tail_thm = (case seb_full_tail of SOME th => th | NONE => raise Fail "seb_full_tail NONE");
fun seb_full_tail_at nT = beta_norm (Drule.infer_instantiate ctxtBL [(("n_sft",0), ctermBL nT)] seb_full_tail_thm);

fun bertrand_large631_body nF h631 =
  let
    (* SEB_HYP n via seb_full_tail *)
    val sebN = Thm.implies_elim (seb_full_tail_at nF) h631   (* SEB_HYP n *)
    (* le 513 n : 513 <= 631 <= n *)
    val le_513_631 = le_evalBL 513 631     (* le 513 631 (513 left arg ; ~513 steps) *)
    val le_513_n = le_transBL_at (mkNum 513, cJ631, nF) le_513_631 h631   (* le 513 n *)
    (* instantiate bertrand_large_given_seb at nF : SEB_HYP ?n ==> le 513 ?n ==> Ex ... *)
    val blgsN = beta_norm (Drule.infer_instantiate ctxtBL
          (map (fn (ix,_) => (ix, ctermBL nF)) blgs_vars) blgs_BL)
    (* discharge SEB then le 513 n via implies_elim (OF chokes on the meta-AND SEB premise) *)
    val gEx = Thm.implies_elim (Thm.implies_elim blgsN sebN) le_513_n
    val d1 = Thm.implies_intr (ctermBL (jT (le cJ631 nF))) gEx
  in d1 end;

val bertrand_large631 =
  (let val nF = Free("n_bl631", natT)
       val h631 = Thm.assume (ctermBL (jT (le cJ631 nF)))
   in SOME (varify (bertrand_large631_body nF h631)) end)
  handle e => (out ("bertrand_large631 EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val bl631_0hyp = (case bertrand_large631 of SOME th => zhBL th | NONE => false);
val bl631_aconv =
  (case bertrand_large631 of
     SOME th =>
       let val nV = Var(("n_bl631",0), natT)
           val bb = Term.lambda (Free("p_bw", natT))
                      (mkConj (prime2 (Free("p_bw", natT)))
                              (mkConj (lt nV (Free("p_bw", natT)))(le (Free("p_bw", natT))(add nV nV))))
           val intended = Logic.mk_implies (jT (le cJ631 nV), jT (mkEx bb))
       in (Thm.prop_of th) aconv intended end
   | NONE => false);
val () = out ("bertrand_large631 0hyp=" ^ Bool.toString bl631_0hyp ^ " aconv=" ^ Bool.toString bl631_aconv ^ "\n");
val () = if bl631_0hyp andalso bl631_aconv then out "BERTRAND_LARGE631_OK\n" else out "BERTRAND_LARGE631_FAIL\n";

(* ============================================================================
   (MAIN)  bertrand_given_chain : [bertrand_chain] ==> bertrand.
     bertrand_chain (ASSUMED here, the EXACT statement) :
        lt 0 n ==> lt n 631 ==> Ex p. prime2 p /\ lt n p /\ le p (2n).
     bertrand : !n. lt 0 n ==> Ex p. prime2 p /\ lt n p /\ le p (2n).
     case-split lt n 631 (chain) vs le 631 n (bertrand_large631).
   ============================================================================ *)
val () = out "MAIN_BEGIN\n";

(* the bertrand_chain statement, META-UNIVERSAL form (over a Free n_chn) :
     !!n. lt 0 n ==> lt n 631 ==> Ex p. prime2 p /\ lt n p /\ le p (2n).
   This is logically the chain.  Assuming this meta-universal lets us forall_elim
   at each specific n (forall_elim does NOT instantiate the hyp), then discharge the
   one meta-universal hyp cleanly.  In the FULL driver the real (schematic) bertrand_chain
   is converted to this meta-universal via Thm.forall_intr before feeding it in. *)
val bcNvar = Free("n_chn", natT);
val bertrand_chain_body =
  let val bb = Term.lambda (Free("p_bw", natT))
        (mkConj (prime2 (Free("p_bw", natT)))
                (mkConj (lt bcNvar (Free("p_bw", natT)))(le (Free("p_bw", natT))(add bcNvar bcNvar))))
  in Logic.mk_implies (jT (lt ZeroC bcNvar),
       Logic.mk_implies (jT (lt bcNvar (mkNum 631)), jT (mkEx bb))) end;
val bertrand_chain_stmt = Logic.all bcNvar bertrand_chain_body;   (* !!n. ... *)
val bertrand_chain_assumed = Thm.assume (ctermBL bertrand_chain_stmt);   (* the ONLY hyp *)
fun bertrand_chain_at nT h0 hlt631 =
  let val inst = beta_norm (Thm.forall_elim (ctermBL nT) bertrand_chain_assumed)   (* lt 0 nT ==> lt nT 631 ==> Ex ... *)
  in Thm.implies_elim (Thm.implies_elim inst h0) hlt631 end;

val bl631_thm = (case bertrand_large631 of SOME th => th | NONE => raise Fail "bertrand_large631 NONE");
fun bl631_at nT h631 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL [(("n_bl631",0), ctermBL nT)] bl631_thm)) h631;

(* the bertrand existential body : Ex p. prime2 p /\ (lt n p /\ le p (2n)) *)
fun bert_body nT = Term.lambda (Free("p_bw", natT))
        (mkConj (prime2 (Free("p_bw", natT)))
                (mkConj (lt nT (Free("p_bw", natT)))(le (Free("p_bw", natT))(add nT nT))));

fun bertrand_inner nF h0 =   (* h0 : lt 0 n ; returns Ex p. ... *)
  let
    val goalEx = mkEx (bert_body nF)
    val tot = le_totalBL (nF, mkNum 630)   (* Disj (le n 630)(le 630 n) *)
    (* CASE lt n 631 : le n 630 -> le (Suc n) 631 -> chain *)
    val caseLt =
      let val hle630 = Thm.assume (ctermBL (jT (le nF (mkNum 630))))
          val hlt631 = le_suc_monoBL_at (nF, mkNum 630) hle630   (* le (Suc n) 631 = lt n 631 *)
          val gEx = bertrand_chain_at nF h0 hlt631
      in Thm.implies_intr (ctermBL (jT (le nF (mkNum 630)))) gEx end
    (* CASE le 631 n : -> bertrand_large631 ; but le 630 n includes n=630 (chain).
       Sub-split le 630 n via le_eq_or_succ : oeq 630 n (n=630, chain) vs le 631 n (large). *)
    val caseGe =
      let val hle630n = Thm.assume (ctermBL (jT (le (mkNum 630) nF)))   (* le 630 n *)
          val dj = le_eq_or_succ_leBL (mkNum 630, nF) hle630n   (* Disj (oeq 630 n)(le 631 n) *)
          val caseEq =
            let val heq = Thm.assume (ctermBL (jT (oeq (mkNum 630) nF)))   (* oeq 630 n *)
                (* n = 630 < 631 : le n 630 from le n n, rewrite 2nd n -> 630 (oeq n 630 = sym heq) *)
                val le_n_630 = le_cong_rBL (nF, nF, mkNum 630) (oeqsymBL heq) (le_reflBL_at nF)   (* le n 630 *)
                val hlt631 = le_suc_monoBL_at (nF, mkNum 630) le_n_630
                val gEx = bertrand_chain_at nF h0 hlt631
            in Thm.implies_intr (ctermBL (jT (oeq (mkNum 630) nF))) gEx end
          val caseLarge =
            let val h631 = Thm.assume (ctermBL (jT (le cJ631 nF)))   (* le 631 n *)
                val gEx = bl631_at nF h631
            in Thm.implies_intr (ctermBL (jT (le cJ631 nF))) gEx end
          val g = disjEBL (oeq (mkNum 630) nF, le cJ631 nF, goalEx) dj caseEq caseLarge
      in Thm.implies_intr (ctermBL (jT (le (mkNum 630) nF))) g end
  in disjEBL (le nF (mkNum 630), le (mkNum 630) nF, goalEx) tot caseLt caseGe end;

(* bertrand : !n. lt 0 n ==> Ex p. ... ; build a universally-quantified (meta) form,
   then discharge bertrand_chain hyp.  We phrase 'bertrand' as the meta-universal
   !!n. lt 0 n ==> Ex ... (object ! not needed for the structural statement). *)
val bertrand_given_chain =
  (let
     val nF = Free("n_bert", natT)
     val h0 = Thm.assume (ctermBL (jT (lt ZeroC nF)))
     val inner = bertrand_inner nF h0
     val d0 = Thm.implies_intr (ctermBL (jT (lt ZeroC nF))) inner   (* lt 0 n ==> Ex ... *)
     val univ = Thm.forall_intr (ctermBL nF) d0                     (* !!n. lt 0 n ==> Ex ... *)
     (* discharge the bertrand_chain hyp *)
     val gc = Thm.implies_intr (ctermBL bertrand_chain_stmt) univ   (* [bertrand_chain] ==> bertrand *)
   in SOME gc end)
  handle e => (out ("bertrand_given_chain EXN : " ^ General.exnMessage e ^ "\n"); NONE);

val () =
  (case bertrand_given_chain of
     SOME th =>
       let val hyps = Thm.hyps_of th val shyps = Thm.extra_shyps th
       in out ("bertrand_given_chain hyps=" ^ Int.toString (length hyps)
               ^ " extra_shyps=" ^ Int.toString (length shyps) ^ "\n")
       end
   | NONE => out "bertrand_given_chain NONE\n");

(* the hyp must be EXACTLY the bertrand_chain statement.  After implies_intr the hyp is
   discharged into the prop, so hyps_of should be [] and extra_shyps []. *)
val bgc_0hyp = (case bertrand_given_chain of SOME th => (null (Thm.hyps_of th) andalso null (Thm.extra_shyps th)) | NONE => false);
(* aconv : the prop is [bertrand_chain_stmt] ==> (!!n. lt 0 n ==> Ex bert_body n) *)
val bgc_aconv =
  (case bertrand_given_chain of
     SOME th =>
       let val nF = Free("n_bert", natT)
           val bertGoal = Logic.all nF (Logic.mk_implies (jT (lt ZeroC nF), jT (mkEx (bert_body nF))))
           val intended = Logic.mk_implies (bertrand_chain_stmt, bertGoal)
       in (Thm.prop_of th) aconv intended end
   | NONE => false);
val () = out ("bertrand_given_chain 0hyp(discharged)=" ^ Bool.toString bgc_0hyp ^ " aconv=" ^ Bool.toString bgc_aconv ^ "\n");
val () = if bgc_0hyp andalso bgc_aconv then out "BERTRAND_GIVEN_CHAIN_OK\n" else out "BERTRAND_GIVEN_CHAIN_FAIL\n";

(* range soundness probe : MAIN must NOT prove the weakened le p n form *)
val bgc_range =
  (case bertrand_given_chain of
     SOME th =>
       let val nF = Free("n_bert", natT)
           val bbW = Term.lambda (Free("p_bw", natT))
                       (mkConj (prime2 (Free("p_bw", natT)))
                               (mkConj (lt nF (Free("p_bw", natT)))(le (Free("p_bw", natT)) nF)))   (* le p n -- wrong *)
           val bertGoalW = Logic.all nF (Logic.mk_implies (jT (lt ZeroC nF), jT (mkEx bbW)))
           val badW = Logic.mk_implies (bertrand_chain_stmt, bertGoalW)
       in not ((Thm.prop_of th) aconv badW) end
   | NONE => false);
val () = if bgc_range then out "BERTRAND_RANGE_PROBE_OK (not the weakened le p n form)\n" else out "BERTRAND_RANGE_PROBE_FAIL\n";

(* ============================================================================
   AXIOM AUDIT : only ex_middle classical + bitlen's 2 conservative eqns.
   NO smuggled bertrand / seb / crude / inequality / prime-existence axiom.
   ============================================================================ *)
val () =
  let
    val thy = Proof_Context.theory_of ctxtBL
    val names = map fst (Theory.all_axioms_of thy)
    val classical = List.filter (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names
    val bitlenAx = List.filter (fn s => String.isSubstring "bitlen" s) names
    val suspicious = List.filter (fn s =>
         String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s
         orelse String.isSubstring "chebyshev" s orelse String.isSubstring "postulate" s
         orelse String.isSubstring "seb" s orelse String.isSubstring "threshold" s
         orelse String.isSubstring "window" s orelse String.isSubstring "crude" s
         orelse String.isSubstring "pow_bound" s orelse String.isSubstring "poly_ineq" s
         orelse String.isSubstring "inequality" s orelse String.isSubstring "chain" s) names
  in out ("JEWEL_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " classical=" ^ Int.toString (length classical)
          ^ " bitlen_axioms=" ^ Int.toString (length bitlenAx)
          ^ " suspicious=" ^ Int.toString (length suspicious) ^ "\n");
     app (fn s => out ("  CLASSICAL: " ^ s ^ "\n")) classical;
     app (fn s => out ("  BITLEN AXIOM: " ^ s ^ "\n")) bitlenAx;
     app (fn s => out ("  SUSPICIOUS AXIOM: " ^ s ^ "\n")) suspicious
  end;

val () = if bgc_0hyp andalso bgc_aconv andalso bgc_range then out "BERTRAND_GIVEN_CHAIN_PROVED\n"
         else out "BERTRAND_GIVEN_CHAIN_NOT_PROVED\n";
val () = out "BERTRAND_JEWEL_DONE\n";

(* ============================================================================
   FULL-DRIVER DISCHARGE RECIPE (UNCONDITIONAL bertrand).
   ----------------------------------------------------------------------------
   The FAST driver assembles (no exit):
       bertrand_f7_full.sml
     + bertrand_w1_appendix.sml          [strip the trailing OS.Process.exit]
     + w1_crude_appendix.sml
     + w1_pow_poly_appendix.sml
     + bertrand_jewel_appendix.sml       [THIS file]
   and ASSUMES bertrand_chain (meta-universal) via Thm.assume — so iteration is fast
   (~6 min : f7 ~5 min + s=35/assembly).  Result : BERTRAND_GIVEN_CHAIN_PROVED, the
   single hyp being EXACTLY the bertrand_chain statement.

   The FULL (unconditional) driver inserts the REAL chain BEFORE this file :
       ... w1_pow_poly_appendix.sml
     + bertrand_ch_appendix.sml          [PROVES bertrand_chain via prime2_via_check up
                                          to 631 ; SLOW ~13 min, needs >=12 GB heap]
     + bertrand_jewel_appendix.sml       [THIS file]
   then the discharge below (run ONLY when the real `bertrand_chain` val is in scope) :

     val bc_real_vars = Term.add_vars (Thm.prop_of bertrand_chain) [];
     val nChainFree = Free("n_chn", natT);
     val bc_inst = beta_norm (Drule.infer_instantiate ctxtBL
           (map (fn (ix,_) => (ix, ctermBL nChainFree)) bc_real_vars) bertrand_chain);
     val bc_meta = Thm.forall_intr (ctermBL nChainFree) bc_inst;   (* !!n. chain *)
       (* bc_meta aconv bertrand_chain_stmt  [validated : DWT_OK] *)
     val bertrand = (case bertrand_given_chain of
         SOME bgc => Thm.implies_elim bgc bc_meta | NONE => raise Fail "bgc");
       (* bertrand : !!n. lt 0 n ==> Ex p. prime2 p /\ lt n p /\ le p (2n)
          0-hyp (real chain is 0-hyp, so the sole chain hyp discharges to nothing),
          aconv bertGoal, axiom audit : only ex_middle + the 2 bitlen eqns. *)

   The discharge WIRING is validated independently (fast) by _discharge_wiring_test.sml :
   feeding bertrand_given_chain an assumed meta-chain yields bertrand = bertGoal with the
   SOLE hyp the chain stmt (DWT_OK).  Replacing the assumed chain with the PROVED one
   (bc_meta from ch_appendix) discharges that hyp -> the UNCONDITIONAL Bertrand's postulate.
   ============================================================================ *)
