
(* ############################################################################
   ####  GAUSS SIGN AS A FLIP COUNT  +  EISENSTEIN LEMMA  (fleet F2c)  #########
   APPENDED to (qr_f1_toolbox.sml ++ qr_f2_appendix.sml ++ qr_f2b_appendix.sml).
   The base ends at QR_F2B_ALL_OK on ctxtU/ctermU/thyU.  F2c closes the LAST
   piece before the lattice symmetry + final law (F3) : it MATERIALISES the Gauss
   sign as a flip COUNT and CLOSES THE EISENSTEIN LEMMA.

   What is already banked on the U-context (0-hyp + aconv):
     gauss_lemma (ctxtGG)  : prime2 p ==> ~(p|a) ==> (p-1=m+m) ==>
                               Ex S. cong p (pow a m) S /\ isSign p S
     eisenstein_parity (U) : (premises) ==> parity(cnt flipPred m)=parity(sum floor)
   Missing : the link  S == (p-1)^(cnt flipPred m)  (mod p).

   Stages (each a GATED _OK marker; graceful floor) :
     (SC) gauss_sign_count : prime2 p ==> ~(p|a) ==> (p-1=m+m) ==>
            Ex S. cong p (pow a m) S /\ isSign p S
                  /\ cong p S (pow (sub p 1) (cnt (flipAbs a p) m))
          marker GAUSS_SIGN_COUNT_OK.
     (PN) pow_neg1_mod : cong p (pow (sub p 1) k) (pow (sub p 1) (parity k))
          marker POW_NEG1_MOD_OK.
     (EL) eisenstein_lemma : prime2 p ==> parity p = 1 ==> prime2 q ==> ~(p|q) ==>
            (p-1=m+m) ==> cong p (pow q m)(pow (sub p 1)(sumf (\k.rdiv(q*k)p) m))
          marker EIS_LEMMA_OK.
   ############################################################################ *)
val () = out "F2C_BEGIN\n";

(* ============================================================================
   cong / pow / sign machinery on ctxtU.  All the cong_* / pow_* / mod_cancel /
   lar_cong / sign / neg_one_mult lemmas are 0-hyp schematic theorems banked on
   earlier contexts; transfer + varify onto ctxtU (schematic 0-hyp theorems
   survive a context change).  cong / congL / congR / isSign / pow / lprod / lmap
   / uptoF / lar are top-level term constructors already in scope.
   ============================================================================ *)
val pow_Zero_U2  = varifyU pow_Zero_ax;     (* oeq (pow a 0)(Suc 0)                  *)
val pow_Suc_U2   = varifyU pow_Suc_ax;      (* oeq (pow a (Suc n))(mult a (pow a n)) *)
val cong_refl_U  = varifyU cong_refl;
val cong_sym_U   = varifyU cong_sym;
val cong_trans_U = varifyU cong_trans;
val cong_mult_U  = varifyU cong_mult;
val cong_pow_U   = varifyU cong_pow;
val mod_cancel_U = varifyU mod_cancel;
val mult_Suc_U   = varifyU mult_Suc;
val () = out "F2C_VARIFY_DONE\n";

(* pow instantiators on ctxtU *)
fun powZero_U at = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU at)] pow_Zero_U2);
fun powSuc_U (at,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("n",0), ctermU nt)] pow_Suc_U2);

(* mult congruence + commutativity helpers on ctxtU (oeq-level) *)
fun mult1l_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_1_left_U);
fun multcomm_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] mult_comm_U);
fun multassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] mult_assoc_U);
fun mult_cong_l_U (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult (Bound 0) kT) (mult qT kT))
  in oeq_rw_U (Pabs, qT, pT) (oeq_sym_U OF [hpq]) (oeqRefl_U (mult qT kT)) end;
fun mult_cong_r_U (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult hT pT)) end;

(* cong instantiators on ctxtU *)
fun cong_refl_U_at (mt, at) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt), (("a",0), ctermU at)] cong_refl_U);
fun cong_sym_U_at (mt, at, bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt), (("a",0), ctermU at), (("b",0), ctermU bt)] cong_sym_U)) h;
fun cong_trans_U_at (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt), (("a",0), ctermU at), (("b",0), ctermU bt), (("c",0), ctermU ct)] cong_trans_U)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_mult_U_at (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt), (("a",0), ctermU at), (("a2",0), ctermU a2t),
         (("b",0), ctermU bt), (("b2",0), ctermU b2t)] cong_mult_U)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_pow_U_at (mt, at, bt, nt) hcong =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt), (("a",0), ctermU at), (("b",0), ctermU bt), (("n",0), ctermU nt)] cong_pow_U)) hcong;
fun mod_cancel_U_at (pt, at, bt, ct) hPrime hNdvd hCong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("b",0), ctermU bt),(("c",0), ctermU ct)] mod_cancel_U)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) hNdvd) hCong end;

(* cong rewrite by an oeq under cong's 2nd/1st arg (built on oeq_rw_U) *)
fun cong_rwR_U p aT (xT, yT) hxy hcong =
  let val zc = Free("z_crwR", natT)
  in oeq_rw_U (Term.lambda zc (cong p aT zc), xT, yT) hxy hcong end;
fun cong_rwL_U p bT (xT, yT) hxy hcong =
  let val zc = Free("z_crwL", natT)
  in oeq_rw_U (Term.lambda zc (cong p zc bT), xT, yT) hxy hcong end;
(* cong_of_oeq : oeq a b ==> cong p a b *)
fun cong_of_oeq_U p (aT, bT) hoeq =
  cong_rwR_U p aT (aT, bT) hoeq (cong_refl_U_at (p, aT));
val () = out "F2C_CONG_INSTANTIATORS_READY\n";

(* clean gate for F2c lemmas *)
fun cleanF2c th = (length (Thm.hyps_of th) = 0) andalso (length (Thm.extra_shyps th) = 0);
fun checkF2c (nm, th, intended) =
  let val ok = cleanF2c th andalso ((Thm.prop_of th) aconv intended)
  in (if ok then out ("OK " ^ nm ^ "\n")
      else (out ("FAIL " ^ nm ^ "\n");
            out ("  got      = " ^ Syntax.string_of_term ctxtU (Thm.prop_of th) ^ "\n");
            out ("  intended = " ^ Syntax.string_of_term ctxtU intended ^ "\n"));
      ok) end;

(* ============================================================================
   prime2 helpers on ctxtU : lt 1 p, lt 0 p  (mirror prime2_gt1_U / lt0_of_prime_U
   already present in F2b).  Reuse the F2b ones (prime2_gt1_U, lt0_of_prime_U).
   ============================================================================ *)

(* ============================================================================
   neg_one_mult / pm1_sq on ctxtU.
     neg_one_mult : prime2 p ==> cong p (add x (mult (sub p 1) x)) 0
     pm1_sq       : prime2 p ==> cong p (mult (sub p 1)(sub p 1)) 1
   These are FUNCTIONS taking hPrime in the base (built per-call from cong_introR
   + arithmetic).  Re-derive pm1_sq directly on ctxtU from neg_one_mult-style
   reasoning, OR transfer the banked neg_one_mult result.  Simpler : both are
   reachable as banked SCHEMATIC theorems?  No -- they are SML functions, not vals.
   So we re-derive pm1_sq on ctxtU from first principles using cong machinery.
   ----------------------------------------------------------------------------
   pm1_sq proof :  (p-1)*(p-1) == 1 (mod p).
   Use neg_one_mult-flavour : (p-1) + (p-1)*(p-1) == 0 (mod p)  [x=(p-1)].
   And (p-1) + 1 == p == 0 (mod p)  i.e.  cong p (add (p-1) 1) 0.
   Then cong p ((p-1)*(p-1)) 1 follows by cancelling (p-1) :
     cong p (add (p-1) ((p-1)*(p-1)))(add (p-1) 1)   [both == 0]
     -> cong p ((p-1)*(p-1)) 1                        [add_left_cancel for cong].
   We instead use the banked recover and cong_introR on ctxtU.  Because the base
   already provides recover_p_r_U + div/mod, the cleanest is to mirror the F1
   pm1_sq DIRECTLY.  To avoid re-deriving neg_one_mult, we build pm1_sq via:
     (p-1)*(p-1) = p*(p-2) + 1   (when p>=1)   ->  cong p ((p-1)^2) 1
   i.e.  oeq ((p-1)*(p-1)) (add 1 (mult p (sub p 2)))  ->  cong_introR with w=(p-2).
   That algebra needs sub facts.  Simplest robust path : transfer the closed
   neg_one_mult / pm1_sq via a small local re-proof using cong_introR_U.
   ============================================================================ *)
(* cong_introR_U : oeq a (add b (mult m w)) ==> cong m a b  (RIGHT disjunct) *)
fun cong_introR_U (m, a, b, w) hyp =
  let
    val RAbs = Abs ("k", natT, oeq a (add b (mult m (Bound 0))));
    val exThm = exI_U_at (RAbs, w) hyp;     (* jT (congR m a b) *)
  in disjI2_U_at (congL m a b, congR m a b) exThm end;
fun cong_introL_U (m, a, b, w) hyp =
  let
    val LAbs = Abs ("k", natT, oeq b (add a (mult m (Bound 0))));
    val exThm = exI_U_at (LAbs, w) hyp;     (* jT (congL m a b) *)
  in disjI1_U_at (congL m a b, congR m a b) exThm end;
val () = out "F2C_CONG_INTRO_READY\n";

(* more arithmetic on ctxtU : sub axioms, right_distrib, mult_1_right, add_left_cancel *)
val sub_n_0_U     = varifyU sub_n_0_ax;
val sub_Suc_Suc_U = varifyU sub_Suc_Suc_ax;
val right_distrib_U = varifyU right_distrib;
val mult_1_right_U  = varifyU mult_1_right;
val add_left_cancel_U = varifyU add_left_cancel;
fun subN0_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] sub_n_0_U);
fun subSS_U (nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("n",0), ctermU nt),(("k",0), ctermU kt)] sub_Suc_Suc_U);
fun rdist_U (aT,bT,kT) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU aT),(("n",0), ctermU bT),(("k",0), ctermU kT)] right_distrib_U);
fun mult1r_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_1_right_U);
fun add0_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] (varifyU add_0));
fun addassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] add_assoc_U);

(* cong_add_cancel_r on ctxtU : cong p (add x r)(add y r) ==> cong p x y
   (mirror cong_add_cancel_r at GG; uses add_left_cancel + rearrangement). *)
fun cong_add_cancel_r_U p x y r hcong =
  let
    val goalC = cong p x y;
    val xr = add x r; val yr = add y r;
    val caseL =
      let
        val LAbs = Abs("k", natT, oeq yr (add xr (mult p (Bound 0))));
        fun body w (hw:thm) =
          let
            val a1 = addassoc_U (x, r, mult p w);                 (* (x+r)+pw = x+(r+pw) *)
            val c1 = addcomm_U (r, mult p w);                     (* (r+pw)=(pw+r) *)
            val c1c = add_cong_r_U (x, add r (mult p w), add (mult p w) r) c1;
            val a2 = addassoc_U (x, mult p w, r);                 (* (x+pw)+r = x+(pw+r) *)
            val a2s = oeq_sym_U OF [a2];
            val rearr = oeq_trans_U OF [oeq_trans_U OF [a1, c1c], a2s]; (* (x+r)+pw = (x+pw)+r *)
            val yr_eq = oeq_trans_U OF [hw, rearr];               (* y+r = (x+pw)+r *)
            (* y+r = (x+pw)+r ; comm both : r+y = r+(x+pw) -> add_left_cancel -> y = x+pw *)
            val cy = addcomm_U (y, r);                            (* (y+r)=(r+y) *)
            val cxpw = addcomm_U (add x (mult p w), r);           (* ((x+pw)+r)=(r+(x+pw)) *)
            val ry_eq = oeq_trans_U OF [oeq_trans_U OF [oeq_sym_U OF [cy], yr_eq], cxpw];
                        (* (r+y) = (r+(x+pw)) *)
            val y_eq = add_left_cancel_U OF [ry_eq];              (* oeq y (x+pw) *)
            val body2 = y_eq;   (* oeq y (add x (mult p w)) : congL p x y body *)
          in cong_introL_U (p, x, y, w) body2 end;
        val exL = Thm.assume (ctermU (jT (mkEx LAbs)));
      in exE_U_at (LAbs, goalC) exL "wL_cac" body end;
    val caseR =
      let
        val RAbs = Abs("k", natT, oeq xr (add yr (mult p (Bound 0))));
        fun body w (hw:thm) =
          let
            val a1 = addassoc_U (y, r, mult p w);
            val c1 = addcomm_U (r, mult p w);
            val c1c = add_cong_r_U (y, add r (mult p w), add (mult p w) r) c1;
            val a2 = addassoc_U (y, mult p w, r);
            val a2s = oeq_sym_U OF [a2];
            val rearr = oeq_trans_U OF [oeq_trans_U OF [a1, c1c], a2s];  (* (y+r)+pw = (y+pw)+r *)
            val xr_eq = oeq_trans_U OF [hw, rearr];               (* x+r = (y+pw)+r *)
            val cx = addcomm_U (x, r);
            val cypw = addcomm_U (add y (mult p w), r);
            val rx_eq = oeq_trans_U OF [oeq_trans_U OF [oeq_sym_U OF [cx], xr_eq], cypw];
            val x_eq = add_left_cancel_U OF [rx_eq];              (* oeq x (y+pw) *)
          in cong_introR_U (p, x, y, w) x_eq end;
        val exR = Thm.assume (ctermU (jT (mkEx RAbs)));
      in exE_U_at (RAbs, goalC) exR "wR_cac" body end;
    val cA = Thm.implies_intr (ctermU (jT (congL p xr yr))) caseL;
    val cB = Thm.implies_intr (ctermU (jT (congR p xr yr))) caseR;
  in disjE_U_at (congL p xr yr, congR p xr yr, goalC) hcong cA cB end;
val () = out "F2C_CANCEL_READY\n";

(* one_plus_pm1_U : prime2 p ==> oeq (add 1 (sub p 1)) p *)
fun one_plus_pm1_U p hPrime =
  let
    val lt0p = lt0_of_prime_U p hPrime;        (* lt 0 p = Ex w. p = (Suc 0) + w *)
    val Pabs = Abs("w", natT, oeq p (add (suc ZeroC) (Bound 0)));
    fun body wF (hw:thm) =
      let
        val aS = addSuc_U (ZeroC, wF);          (* (Suc 0 + w) = Suc(0 + w) *)
        val a0 = add0_U wF;                      (* (0+w)=w *)
        val pSucw = oeq_trans_U OF [oeq_trans_U OF [hw, aS], Succong_U a0];  (* p = Suc w *)
        val ss = subSS_U (wF, ZeroC);           (* sub (Suc w)(Suc 0) = sub w 0 *)
        val sn0 = subN0_U wF;                   (* sub w 0 = w *)
        val sub_Sw_eq_w = oeq_trans_U OF [ss, sn0];  (* sub (Suc w) 1 = w *)
        val zsp = Free("z_oppU", natT);
        val sub_p1_w = oeq_rw_U (Term.lambda zsp (oeq (sub zsp oneC) wF), suc wF, p)
                         (oeq_sym_U OF [pSucw]) sub_Sw_eq_w;       (* sub p 1 = w *)
        val r1 = add_cong_r_U (suc ZeroC, sub p oneC, wF) sub_p1_w;  (* (1 + (p-1)) = (1 + w) *)
        val r2 = addSuc_U (ZeroC, wF);          (* (Suc 0 + w) = Suc(0+w) *)
        val r3 = Succong_U a0;                  (* Suc(0+w) = Suc w *)
        val one_w_eq_p = oeq_trans_U OF [oeq_trans_U OF [oeq_trans_U OF [r1, r2], r3], oeq_sym_U OF [pSucw]];
      in one_w_eq_p end;
  in exE_U_at (Pabs, oeq (add (suc ZeroC)(sub p oneC)) p) lt0p "w_oppU" body end;

(* p_mult_zero_U : cong p (mult p x) 0 *)
fun p_mult_zero_U p x =
  let
    val a0 = add0_U (mult p x);    (* (0 + p*x) = p*x *)
    val body = oeq_sym_U OF [a0];  (* (p*x) = (0 + p*x) *)
  in cong_introR_U (p, mult p x, ZeroC, x) body end;

(* pm1_sq_U : prime2 p ==> cong p (mult (sub p 1)(sub p 1)) 1 *)
fun pm1_sq_U p hPrime =
  let
    val pm1 = sub p oneC;
    (* neg_one_mult at x=(p-1) : cong p ((p-1) + (p-1)*(p-1)) 0 *)
    val opp = one_plus_pm1_U p hPrime;          (* (1 + (p-1)) = p *)
    val x = pm1;
    val lcong = mult_cong_l_U (add (suc ZeroC)(sub p oneC), p, x) opp;  (* ((1+(p-1))*x)=(p*x) *)
    val rd = rdist_U (suc ZeroC, sub p oneC, x);  (* ((1+(p-1))*x) = (1*x + (p-1)*x) *)
    val m1 = mult1l_U x;                          (* (1*x) = x *)
    val rd_x = add_cong_l_U (mult (suc ZeroC) x, x, mult (sub p oneC) x) m1;
                  (* (1*x + (p-1)*x) = (x + (p-1)*x) *)
    val sum_eq_px = oeq_trans_U OF [oeq_sym_U OF [oeq_trans_U OF [rd, rd_x]], lcong];
                  (* (x + (p-1)*x) = (p*x) *)
    val pmz = p_mult_zero_U p x;                  (* cong p (p*x) 0 *)
    val zc = Free("z_nomU", natT);
    val nom = oeq_rw_U (Term.lambda zc (cong p zc ZeroC), mult p x, add x (mult (sub p oneC) x))
                (oeq_sym_U OF [sum_eq_px]) pmz;  (* cong p ((p-1) + (p-1)*(p-1)) 0 *)
    (* reorder LHS to ((p-1)*(p-1) + (p-1)) *)
    val comm = addcomm_U (pm1, mult pm1 pm1);
    val nom2 = oeq_rw_U (Term.lambda zc (cong p zc ZeroC), add pm1 (mult pm1 pm1), add (mult pm1 pm1) pm1) comm nom;
                 (* cong p ((p-1)*(p-1) + (p-1)) 0 *)
    (* cong p (1+(p-1)) 0 : 1+(p-1)=p, cong p p 0 *)
    val pm1r = mult1r_U p;                        (* (p*1) = p *)
    val pmz1 = p_mult_zero_U p (suc ZeroC);       (* cong p (p*1) 0 *)
    val congp0 = oeq_rw_U (Term.lambda zc (cong p zc ZeroC), mult p (suc ZeroC), p) pm1r pmz1;  (* cong p p 0 *)
    val cong_1pm1_0 = oeq_rw_U (Term.lambda zc (cong p zc ZeroC), p, add (suc ZeroC) pm1)
                        (oeq_sym_U OF [opp]) congp0;   (* cong p (1 + (p-1)) 0 *)
    val sym01 = cong_sym_U_at (p, add (suc ZeroC) pm1, ZeroC) cong_1pm1_0;  (* cong p 0 (1+(p-1)) *)
    val both = cong_trans_U_at (p, add (mult pm1 pm1) pm1, ZeroC, add (suc ZeroC) pm1) nom2 sym01;
                 (* cong p ((p-1)^2 + (p-1)) (1 + (p-1)) *)
    val cancel = cong_add_cancel_r_U p (mult pm1 pm1) (suc ZeroC) pm1 both;  (* cong p ((p-1)^2) 1 *)
  in cancel end;
val () = out "F2C_PM1SQ_READY\n";

(* sanity smoke : pm1_sq_U on a Free p (0-hyp mod prime2 assumption) *)
val () =
  let
    val pSm = Free("p", natT);
    val hPr = Thm.assume (ctermU (jT (prime2 pSm)));
    val sq = pm1_sq_U pSm hPr;
    val okSq = ((Thm.prop_of sq) aconv (jT (cong pSm (mult (sub pSm oneC)(sub pSm oneC)) oneC)));
    val cleanMod = (length (Thm.hyps_of sq) = 1) andalso (length (Thm.extra_shyps sq) = 0);
  in out ("F2C_PM1SQ_SMOKE okSq=" ^ Bool.toString okSq ^ " cleanMod=" ^ Bool.toString cleanMod ^ "\n") end;

(* sub-1 ground facts on ctxtU *)
val sub1_0_U = subN0_U oneC;                                  (* sub 1 0 = 1 *)
val sub0_0_U = subN0_U ZeroC;                                 (* sub 0 0 = 0 *)
val subSS_11_U = subSS_U (ZeroC, ZeroC);                      (* sub (Suc 0)(Suc 0) = sub 0 0 *)
val sub1_1_U = oeq_trans_U OF [subSS_11_U, sub0_0_U];         (* sub 1 1 = 0 *)
(* parity 1 = 1 on ctxtU *)
val parity1_eq_U2 =
  let
    val pS = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU ZeroC)] parity_Suc_U);
            (* parity(Suc 0) = sub 1 (parity 0) *)
    val subAbs = Abs("z", natT, oeq (sub oneC (parity ZeroC)) (sub oneC (Bound 0)));
    val congP = oeq_rw_U (subAbs, parity ZeroC, ZeroC) parity_0_U (oeqRefl_U (sub oneC (parity ZeroC)));
    val step = oeq_trans_U OF [pS, congP];     (* parity(Suc 0) = sub 1 0 *)
  in oeq_trans_U OF [step, sub1_0_U] end;      (* parity(Suc 0) = 1 *)

(* ############################################################################
   ##########  (PN)  pow_neg1_mod : (p-1)^k == (p-1)^(parity k) (mod p)  #######
   cong p (pow (sub p 1) k)(pow (sub p 1)(parity k)).
   nat-induction on k.  base k=0 : parity 0 = 0, cong_refl.
   step : IH cong p (pow pm1 k)(pow pm1 (parity k)).
     pow pm1 (Suc k) = pm1 * pow pm1 k          [pow_Suc]
       == pm1 * pow pm1 (parity k)              [cong_mult, IH]
       = pow pm1 (Suc(parity k))                [pow_Suc sym]
     so cong p (pow pm1 (Suc k))(pow pm1 (Suc(parity k))).
     case parity k = 0 : Suc(parity k)=1, parity(Suc k)=sub 1 0 = 1, equal -> done.
     case parity k = 1 : Suc(parity k)=2, parity(Suc k)=sub 1 1 = 0;
        cong p (pow pm1 2)(pow pm1 0) via pm1_sq.
   ############################################################################ *)
val () = out "STAGE_PN_BEGIN\n";
val pow_neg1_mod =
  let
    val pF = Free("p", natT); val kF = Free("k", natT);
    val hPrime = Thm.assume (ctermU (jT (prime2 pF)));
    val pm1 = sub pF oneC;
    val sq = pm1_sq_U pF hPrime;   (* cong p (mult pm1 pm1) 1 *)
    (* cong unfolds to Disj of Ex-binders; a literal Bound 0 would be captured.
       Build Pabs over a FRESH Free (de-Bruijn capture trap). *)
    val zPn = Free("z_pnPred", natT);
    val Pabs = Term.lambda zPn (cong pF (pow pm1 zPn) (pow pm1 (parity zPn)));
    (* base k=0 : parity 0 = 0 ; cong p (pow pm1 0)(pow pm1 0) refl ; rewrite parity 0 -> 0 *)
    val baseThm =
      let
        val cr = cong_refl_U_at (pF, pow pm1 ZeroC);   (* cong p (pow pm1 0)(pow pm1 0) *)
        val zc = Free("z_pnb", natT);
        val rw = oeq_rw_U (Term.lambda zc (cong pF (pow pm1 ZeroC)(pow pm1 zc)), ZeroC, parity ZeroC)
                   (oeq_sym_U OF [parity_0_U]) cr;
                 (* cong p (pow pm1 0)(pow pm1 (parity 0)) *)
      in rw end;
    (* step *)
    val xF = Free("x_pn", natT);
    val ihP = jT (cong pF (pow pm1 xF)(pow pm1 (parity xF)));
    val IH  = Thm.assume (ctermU ihP);
    val stepConcl =
      let
        (* pow pm1 (Suc x) = pm1 * pow pm1 x *)
        val psSx = powSuc_U (pm1, xF);    (* oeq (pow pm1 (Suc x))(mult pm1 (pow pm1 x)) *)
        (* cong p (pm1 * pow pm1 x)(pm1 * pow pm1 (parity x)) via cong_mult (refl on pm1, IH) *)
        val crpm1 = cong_refl_U_at (pF, pm1);
        val cm = cong_mult_U_at (pF, pm1, pm1, pow pm1 xF, pow pm1 (parity xF)) crpm1 IH;
                 (* cong p (mult pm1 (pow pm1 x))(mult pm1 (pow pm1 (parity x))) *)
        (* rewrite both sides via psSx and pow_Suc(parity x) sym to pow form *)
        val psSpx = powSuc_U (pm1, parity xF);  (* oeq (pow pm1 (Suc(parity x)))(mult pm1 (pow pm1 (parity x))) *)
        (* cong p (pow pm1 (Suc x))(pow pm1 (Suc(parity x))) :
           start cm : cong p (mult pm1 (pow pm1 x))(mult pm1 (pow pm1 (parity x)))
           rewrite LHS mult.. -> pow pm1 (Suc x) via psSx sym ; rewrite RHS mult.. -> pow pm1 (Suc(parity x)) via psSpx sym *)
        val cm1 = cong_rwL_U pF (mult pm1 (pow pm1 (parity xF)))
                    (mult pm1 (pow pm1 xF), pow pm1 (suc xF)) (oeq_sym_U OF [psSx]) cm;
                  (* cong p (pow pm1 (Suc x))(mult pm1 (pow pm1 (parity x))) *)
        val cm2 = cong_rwR_U pF (pow pm1 (suc xF))
                    (mult pm1 (pow pm1 (parity xF)), pow pm1 (suc (parity xF))) (oeq_sym_U OF [psSpx]) cm1;
                  (* cong p (pow pm1 (Suc x))(pow pm1 (Suc(parity x))) *)
        (* now bridge cong p (pow pm1 (Suc(parity x)))(pow pm1 (parity(Suc x))) by case on parity x *)
        val pb = parity_bounded_U_at xF;   (* Disj (parity x = 0)(parity x = 1) *)
        val psucx = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU xF)] parity_Suc_U);
                    (* parity(Suc x) = sub 1 (parity x) *)
        val goalBridge = cong pF (pow pm1 (suc (parity xF)))(pow pm1 (parity (suc xF)));
        val cA =
          let
            val hz = Thm.assume (ctermU (jT (oeq (parity xF) ZeroC)));
            (* parity(Suc x) = sub 1 (parity x) = sub 1 0 = 1 = Suc(parity x) [parity x=0] *)
            val subAbs = Abs("z", natT, oeq (sub oneC (parity xF)) (sub oneC (Bound 0)));
            val cg = oeq_rw_U (subAbs, parity xF, ZeroC) hz (oeqRefl_U (sub oneC (parity xF)));
            val psucx1 = oeq_trans_U OF [oeq_trans_U OF [psucx, cg], sub1_0_U];  (* parity(Suc x) = 1 *)
            (* Suc(parity x) = Suc 0 = 1 [parity x = 0] *)
            val sucpx = Succong_U hz;   (* Suc(parity x) = Suc 0 = 1 *)
            (* both Suc(parity x) and parity(Suc x) equal 1 -> equal each other *)
            val eq = oeq_trans_U OF [sucpx, oeq_sym_U OF [psucx1]];  (* Suc(parity x) = parity(Suc x) *)
            (* cong p (pow pm1 (Suc(parity x)))(pow pm1 (parity(Suc x))) via cong_refl + rewrite arg *)
            val cr = cong_refl_U_at (pF, pow pm1 (suc (parity xF)));
            val zc = Free("z_pnA", natT);
            val br = oeq_rw_U (Term.lambda zc (cong pF (pow pm1 (suc (parity xF)))(pow pm1 zc)),
                        suc (parity xF), parity (suc xF)) eq cr;
          in Thm.implies_intr (ctermU (jT (oeq (parity xF) ZeroC))) br end;
        val cB =
          let
            val ho = Thm.assume (ctermU (jT (oeq (parity xF) oneC)));
            (* parity(Suc x) = sub 1 (parity x) = sub 1 1 = 0 [parity x=1] *)
            val subAbs = Abs("z", natT, oeq (sub oneC (parity xF)) (sub oneC (Bound 0)));
            val cg = oeq_rw_U (subAbs, parity xF, oneC) ho (oeqRefl_U (sub oneC (parity xF)));
            val psucx0 = oeq_trans_U OF [oeq_trans_U OF [psucx, cg], sub1_1_U];  (* parity(Suc x) = 0 *)
            (* Suc(parity x) = Suc 1 [parity x=1] ; pow pm1 (Suc 1) = pm1 * pow pm1 1 = pm1 * (pm1 * pow pm1 0)
               and pm1*pm1 == 1 [pm1_sq] ; pow pm1 0 = 1 ; so pow pm1 2 == pm1*pm1*1 == 1 = pow pm1 0.
               We build cong p (pow pm1 (Suc 1))(pow pm1 0) then move endpoints. *)
            (* pow pm1 2 = pm1 * pow pm1 1 [pow_Suc] ; pow pm1 1 = pm1 * pow pm1 0 [pow_Suc] ;
               pow pm1 0 = 1 [pow_Zero] *)
            val two = suc (suc ZeroC);
            val ps2 = powSuc_U (pm1, suc ZeroC);   (* pow pm1 2 = pm1 * pow pm1 1 *)
            val ps1 = powSuc_U (pm1, ZeroC);       (* pow pm1 1 = pm1 * pow pm1 0 *)
            val pz0 = powZero_U pm1;               (* pow pm1 0 = 1 *)
            (* pow pm1 1 = pm1 * 1 [rewrite pow pm1 0 -> 1] = pm1 [mult1r] *)
            val ps1b = let val zc=Free("z_p1",natT)
                       in oeq_rw_U (Term.lambda zc (oeq (pow pm1 (suc ZeroC))(mult pm1 zc)), pow pm1 ZeroC, oneC) pz0 ps1 end;
                       (* pow pm1 1 = pm1 * 1 *)
            val ps1c = oeq_trans_U OF [ps1b, mult1r_U pm1];   (* pow pm1 1 = pm1 *)
            (* pow pm1 2 = pm1 * pow pm1 1 = pm1 * pm1 [rewrite via ps1c] *)
            val ps2b = let val zc=Free("z_p2",natT)
                       in oeq_rw_U (Term.lambda zc (oeq (pow pm1 two)(mult pm1 zc)), pow pm1 (suc ZeroC), pm1) ps1c ps2 end;
                       (* pow pm1 2 = pm1 * pm1 *)
            (* cong p (pow pm1 2)(pm1*pm1) via cong_of_oeq ; cong p (pm1*pm1) 1 via pm1_sq ; trans *)
            val cong22 = cong_of_oeq_U pF (pow pm1 two, mult pm1 pm1) ps2b;  (* cong p (pow pm1 2)(pm1*pm1) *)
            val cong2_1 = cong_trans_U_at (pF, pow pm1 two, mult pm1 pm1, oneC) cong22 sq;  (* cong p (pow pm1 2) 1 *)
            (* cong p (pow pm1 2)(pow pm1 0) : rewrite 1 -> pow pm1 0 (pz0 sym) on RHS *)
            val cong2_0 = cong_rwR_U pF (pow pm1 two) (oneC, pow pm1 ZeroC) (oeq_sym_U OF [pz0]) cong2_1;
                          (* cong p (pow pm1 2)(pow pm1 0) *)
            (* Suc(parity x) = Suc 1 = 2 [parity x = 1] ; rewrite LHS arg Suc(parity x)->2 ;
               parity(Suc x) = 0 ; rewrite RHS arg 0 -> parity(Suc x) *)
            val sucpx_eq2 = Succong_U ho;   (* Suc(parity x) = Suc 1 = 2 *)
            val zc1 = Free("z_pnB1", natT);
            val br1 = oeq_rw_U (Term.lambda zc1 (cong pF (pow pm1 zc1)(pow pm1 ZeroC)), two, suc (parity xF))
                        (oeq_sym_U OF [sucpx_eq2]) cong2_0;
                      (* cong p (pow pm1 (Suc(parity x)))(pow pm1 0) *)
            val zc2 = Free("z_pnB2", natT);
            val br2 = oeq_rw_U (Term.lambda zc2 (cong pF (pow pm1 (suc (parity xF)))(pow pm1 zc2)), ZeroC, parity (suc xF))
                        (oeq_sym_U OF [psucx0]) br1;
                      (* cong p (pow pm1 (Suc(parity x)))(pow pm1 (parity(Suc x))) *)
          in Thm.implies_intr (ctermU (jT (oeq (parity xF) oneC))) br2 end;
        val bridge = disjE_U_at (oeq (parity xF) ZeroC, oeq (parity xF) oneC, goalBridge) pb cA cB;
        (* combine cm2 : cong p (pow pm1(Suc x))(pow pm1(Suc(parity x)))
                + bridge : cong p (pow pm1(Suc(parity x)))(pow pm1(parity(Suc x)))
           -> cong p (pow pm1(Suc x))(pow pm1(parity(Suc x))) [cong_trans] *)
        val res = cong_trans_U_at (pF, pow pm1 (suc xF), pow pm1 (suc (parity xF)), pow pm1 (parity (suc xF))) cm2 bridge;
      in res end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU ihP) stepConcl);
    val run = nat_induct_U_run Pabs kF baseThm stepF;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) run;
  in varify d1 end;
val () = out "STAGE_PN_RAW\n";
val pV_pn = Var(("p",0),natT); val kV_pn = Var(("k",0),natT);
val i_pow_neg1_mod =
  Logic.mk_implies (jT (prime2 pV_pn),
    jT (cong pV_pn (pow (sub pV_pn oneC) kV_pn)(pow (sub pV_pn oneC)(parity kV_pn))));
val r_pow_neg1_mod = checkF2c ("pow_neg1_mod", pow_neg1_mod, i_pow_neg1_mod);
(* soundness probe : dropping prime2 must change the statement *)
val probe_pn_needs_prime =
  let val bogus = jT (cong pV_pn (pow (sub pV_pn oneC) kV_pn)(pow (sub pV_pn oneC)(parity kV_pn)))
  in not ((Thm.prop_of pow_neg1_mod) aconv bogus) end;
val () = if probe_pn_needs_prime then out "PROBE_OK pow_neg1_mod keeps prime2\n"
         else out "PROBE_FAIL pow_neg1_mod\n";
fun pow_neg1_mod_at (pt, kt) hPrime =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt),(("k",0), ctermU kt)] (toU pow_neg1_mod))) hPrime;
val () = if r_pow_neg1_mod andalso probe_pn_needs_prime then out "POW_NEG1_MOD_OK\n" else out "POW_NEG1_MOD_FAILED\n";
val () = out "STAGE_PN_END\n";

(* ############################################################################
   ##########  (SC)  gauss_sign_count  ########################################
   prime2 p ==> ~(p|a) ==> oeq(sub p 1)(add m m) ==>
     cong p (pow a m) (pow (sub p 1) (cnt (flipAbs a p) m))     [a^m == (p-1)^mu mod p]
   Re-run the prod_split_sign induction tracking the running flip COUNT.  We carry
   a STRENGTHENED existential body : Ex S. cong p (LHSp n)(mult S (RHSp n))
                                          /\ isSign p S
                                          /\ cong p S (pow (sub p 1)(cnt flP n)).
   The branch is taken on the TRICHOTOMY le_or_lt(2r,p) (the flipPred level), so we
   simultaneously derive the per-element value-cong (via lar_lo/lar_hi + cong_introR,
   NO coprimality needed -- the lar_cong disjunction proof never used ~(p|k)) AND
   the flipPred status that drives cnt :
     lower (le 2r p) : sk=1   , ~flipPred -> cnt unchanged   -> S stays (p-1)^cnt
     upper (lt p 2r) : sk=p-1 , flipPred  -> cnt increments  -> S *= (p-1)
   Then the same m! cancellation as gauss_lemma turns LHSp/RHSp into a^m.
   ############################################################################ *)
val () = out "STAGE_SC_BEGIN\n";

(* ---- lprod instantiators on ctxtU ---- *)
val lprod_nil_U  = varifyU lprod_nil_ax;
val lprod_cons_U = varifyU lprod_cons_ax;
fun lprodNil_U () = lprod_nil_U;
fun lprodCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] lprod_cons_U);
fun lprod_cong_U (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (lprod aT)) end;

(* ---- le_intro / le_self_suc / lt_0_suc on ctxtU ---- *)
val add_Suc_right_U = varifyU add_Suc_right;
fun addSr_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_Suc_right_U);
fun le_intro_U (mT, nT, w) hyp =
  let val LAbs = Abs ("p", natT, oeq nT (add mT (Bound 0)))
  in exI_U_at (LAbs, w) hyp end;
fun lt_0_suc_U nt =
  let
    val aS = addSuc_U (ZeroC, nt);
    val a0 = add0_U nt;
    val sc = Succong_U a0;
    val sum = oeq_trans_U OF [aS, sc];
    val sum_s = oeq_sym_U OF [sum];
  in le_intro_U (suc ZeroC, suc nt, nt) sum_s end;
fun le_self_suc_U nt =
  let
    val aSr = addSr_U (nt, ZeroC);
    val a0r = add0r_U nt;
    val sa0r = Succong_U a0r;
    val sum = oeq_trans_U OF [aSr, sa0r];
    val sum_s = oeq_sym_U OF [sum];
  in le_intro_U (nt, suc nt, suc ZeroC) sum_s end;

(* ---- sign machinery on ctxtU ---- *)
fun sign_one_U p = disjI1_U_at (cong p oneC oneC, cong p oneC (sub p oneC)) (cong_refl_U_at (p, oneC));
fun sign_pm1_U p = disjI2_U_at (cong p (sub p oneC) oneC, cong p (sub p oneC)(sub p oneC))
                     (cong_refl_U_at (p, sub p oneC));
fun sign_close_U p s1 s2 hPrime hS1 hS2 =
  let
    val pm1 = sub p oneC;
    val goalC = isSign p (mult s1 s2);
    fun mul_cong (c1, c2) h1 h2 = cong_mult_U_at (p, s1, c1, s2, c2) h1 h2;
    fun rwR (xT, yT) hxy hcong = cong_rwR_U p (mult s1 s2) (xT, yT) hxy hcong;
    fun caseS1_one h1 =
      let
        fun caseS2_one h2 =
          let val mc = mul_cong (oneC, oneC) h1 h2
              val m11 = mult1l_U oneC
              val c1 = rwR (mult oneC oneC, oneC) m11 mc
          in disjI1_U_at (cong p (mult s1 s2) oneC, cong p (mult s1 s2) pm1) c1 end
        fun caseS2_pm1 h2 =
          let val mc = mul_cong (oneC, pm1) h1 h2
              val m1 = mult1l_U pm1
              val c1 = rwR (mult oneC pm1, pm1) m1 mc
          in disjI2_U_at (cong p (mult s1 s2) oneC, cong p (mult s1 s2) pm1) c1 end
        val cA = Thm.implies_intr (ctermU (jT (cong p s2 oneC))) (caseS2_one (Thm.assume (ctermU (jT (cong p s2 oneC)))))
        val cB = Thm.implies_intr (ctermU (jT (cong p s2 pm1))) (caseS2_pm1 (Thm.assume (ctermU (jT (cong p s2 pm1)))))
      in disjE_U_at (cong p s2 oneC, cong p s2 pm1, goalC) hS2 cA cB end
    fun caseS1_pm1 h1 =
      let
        fun caseS2_one h2 =
          let val mc = mul_cong (pm1, oneC) h1 h2
              val m1r = mult1r_U pm1
              val c1 = rwR (mult pm1 oneC, pm1) m1r mc
          in disjI2_U_at (cong p (mult s1 s2) oneC, cong p (mult s1 s2) pm1) c1 end
        fun caseS2_pm1 h2 =
          let val mc = mul_cong (pm1, pm1) h1 h2
              val sq = pm1_sq_U p hPrime
              val c1 = cong_trans_U_at (p, mult s1 s2, mult pm1 pm1, oneC) mc sq
          in disjI1_U_at (cong p (mult s1 s2) oneC, cong p (mult s1 s2) pm1) c1 end
        val cA = Thm.implies_intr (ctermU (jT (cong p s2 oneC))) (caseS2_one (Thm.assume (ctermU (jT (cong p s2 oneC)))))
        val cB = Thm.implies_intr (ctermU (jT (cong p s2 pm1))) (caseS2_pm1 (Thm.assume (ctermU (jT (cong p s2 pm1)))))
      in disjE_U_at (cong p s2 oneC, cong p s2 pm1, goalC) hS2 cA cB end
    val cAA = Thm.implies_intr (ctermU (jT (cong p s1 oneC))) (caseS1_one (Thm.assume (ctermU (jT (cong p s1 oneC)))))
    val cBB = Thm.implies_intr (ctermU (jT (cong p s1 pm1))) (caseS1_pm1 (Thm.assume (ctermU (jT (cong p s1 pm1)))))
  in disjE_U_at (cong p s1 oneC, cong p s1 pm1, goalC) hS1 cAA cBB end;

(* ---- neg_one_mult on ctxtU : cong p (add x (mult (sub p 1) x)) 0 ---- *)
fun neg_one_mult_U p x hPrime =
  let
    val opp = one_plus_pm1_U p hPrime;          (* (1 + (p-1)) = p *)
    val lcong = mult_cong_l_U (add (suc ZeroC)(sub p oneC), p, x) opp;  (* ((1+(p-1))*x)=(p*x) *)
    val rd = rdist_U (suc ZeroC, sub p oneC, x);  (* ((1+(p-1))*x)=(1*x + (p-1)*x) *)
    val m1 = mult1l_U x;                          (* (1*x) = x *)
    val rd_x = add_cong_l_U (mult (suc ZeroC) x, x, mult (sub p oneC) x) m1;
    val sum_eq_px = oeq_trans_U OF [oeq_sym_U OF [oeq_trans_U OF [rd, rd_x]], lcong];
    val pmz = p_mult_zero_U p x;                  (* cong p (p*x) 0 *)
    val zc = Free("z_nomU2", natT);
    val res = oeq_rw_U (Term.lambda zc (cong p zc ZeroC), mult p x, add x (mult (sub p oneC) x))
                (oeq_sym_U OF [sum_eq_px]) pmz;
  in res end;

(* ---- mult4_swap on ctxtU : (A*B)*(C*D) = (A*C)*(B*D) ---- *)
fun mult4_swap_U (A,B,C,D) =
  let
    val e1 = multassoc_U (A, B, mult C D);            (* (A*B)*(C*D) = A*(B*(C*D)) *)
    val i1 = oeq_sym_U OF [multassoc_U (B, C, D)];    (* B*(C*D) = (B*C)*D *)
    val e2 = mult_cong_r_U (A, mult B (mult C D), mult (mult B C) D) i1;
    val cm = multcomm_U (B, C);
    val cmL = mult_cong_l_U (mult B C, mult C B, D) cm;
    val e3 = mult_cong_r_U (A, mult (mult B C) D, mult (mult C B) D) cmL;
    val i2 = multassoc_U (C, B, D);
    val e4 = mult_cong_r_U (A, mult (mult C B) D, mult C (mult B D)) i2;
    val e5 = oeq_sym_U OF [multassoc_U (A, C, mult B D)];
  in oeq_trans_U OF [e1, oeq_trans_U OF [e2, oeq_trans_U OF [e3, oeq_trans_U OF [e4, e5]]]] end;
val () = out "STAGE_SC_HELPERS_READY\n";

(* ---- cong_introR_U arithmetic for the lower/upper lar branches (re-derive the
        lar_cong case bodies inline, on ctxtU; NO coprimality used) ---- *)
(* lowerCong : le (2r) p ==> cong p (a*k)(lar a p k)   [lar = r ; a*k = r + p*q] *)
fun lar_value_lower_U (aF, pF, kF) hpos hle =
  let
    val akT = mult aF kF;
    val rT  = rmod akT pF;  val qT = rdiv akT pF;
    val larT = lar aF pF kF;
    val divEq = div_mod_eq_U_at (akT, pF) hpos;   (* a*k = (p*q + r) *)
    val divEq2 = oeq_trans_U OF [divEq, addcomm_U (mult pF qT, rT)];  (* a*k = (r + p*q) *)
    val larEq = lar_lo_U_at (aF, pF, kF) hle;     (* lar = r *)
    val congAkR = cong_introR_U (pF, akT, rT, qT) divEq2;   (* cong p (a*k) r *)
    val congAkLar = cong_rwR_U pF akT (rT, larT) (oeq_sym_U OF [larEq]) congAkR;
  in congAkLar end;   (* cong p (a*k)(lar) *)
(* upperCong : lt p (2r) ==> cong p (a*k + lar a p k) 0   [lar = p-r] *)
fun lar_value_upper_U (aF, pF, kF) hpos hlt =
  let
    val akT = mult aF kF;
    val rT  = rmod akT pF;  val qT = rdiv akT pF;
    val larT = lar aF pF kF;
    val srT  = sub pF rT;
    val divEq = div_mod_eq_U_at (akT, pF) hpos;
    val divEq2 = oeq_trans_U OF [divEq, addcomm_U (mult pF qT, rT)];  (* a*k = (r + p*q) *)
    val larEq = lar_hi_U_at (aF, pF, kF) hlt;     (* lar = p-r *)
    val rltp = rmod_lt_U_at (akT, pF) hpos;       (* lt r p *)
    val goalC = cong pF (add akT larT) ZeroC;
    fun cont wF hPeq hSub =     (* hPeq : oeq p (add r (sub p r)) *)
      let
        val zF = Free("z_hiXU", natT);
        val Xrw = oeq_rw_U (Term.lambda zF (oeq (add akT srT) (add zF srT)), akT, add rT (mult pF qT))
                     divEq2 (oeqRefl_U (add akT srT));   (* X = (r + p*q)+(p-r) *)
        val s_assoc = addassoc_U (rT, mult pF qT, srT);  (* ((r+p*q)+(p-r)) = (r+(p*q+(p-r))) *)
        val s_comm = addcomm_U (mult pF qT, srT);        (* (p*q+(p-r))=((p-r)+p*q) *)
        val zc = Free("z_hiCU", natT);
        val s1 = oeq_rw_U (Term.lambda zc (oeq (add rT (add (mult pF qT) srT)) (add rT zc)),
                    add (mult pF qT) srT, add srT (mult pF qT)) s_comm
                    (oeqRefl_U (add rT (add (mult pF qT) srT)));
        val s_assoc2 = oeq_sym_U OF [addassoc_U (rT, srT, mult pF qT)];
        val s_rpr = oeq_sym_U OF [hPeq];                 (* (r + (p-r)) = p *)
        val s_rpr_pq = oeq_rw_U (Term.lambda zc (oeq (add (add rT srT) (mult pF qT)) (add zc (mult pF qT))),
                    add rT srT, pF) s_rpr (oeqRefl_U (add (add rT srT)(mult pF qT)));
        val chain = oeq_trans_U OF [Xrw,
                      oeq_trans_U OF [s_assoc,
                        oeq_trans_U OF [s1,
                          oeq_trans_U OF [s_assoc2, s_rpr_pq]]]];   (* X = (p + p*q) *)
        val mc1 = multcomm_U (pF, suc qT);               (* (p*(Suc q)) = ((Suc q)*p) *)
        val msuc = beta_norm (Drule.infer_instantiate ctxtU
              [(("m",0), ctermU qT), (("n",0), ctermU pF)] mult_Suc_U);  (* (Suc q * p)=add p (q*p) *)
        val mc2 = multcomm_U (qT, pF);                   (* (q*p)=(p*q) *)
        val s_pqp = oeq_rw_U (Term.lambda zc (oeq (add pF (mult qT pF)) (add pF zc)),
                    mult qT pF, mult pF qT) mc2 (oeqRefl_U (add pF (mult qT pF)));
        val mSucEq = oeq_trans_U OF [oeq_trans_U OF [mc1, msuc], s_pqp];  (* (p*(Suc q)) = (p + p*q) *)
        val Xeq_mSuc = oeq_trans_U OF [chain, oeq_sym_U OF [mSucEq]];  (* X = (p*(Suc q)) *)
        val add0eq = oeq_sym_U OF [add0_U (mult pF (suc qT))];        (* (p*(Suc q)) = (0 + p*(Suc q)) *)
        val Xeq_final = oeq_trans_U OF [Xeq_mSuc, add0eq];           (* X = (0 + p*(Suc q)) *)
        val congX0 = cong_introR_U (pF, add akT srT, ZeroC, suc qT) Xeq_final;  (* cong p (a*k+(p-r)) 0 *)
        (* rewrite (p-r) -> lar inside cong's FIRST arg (add a*k (p-r)) *)
        val zF2 = Free("z_hiLU", natT);
        val congLar0b = oeq_rw_U (Term.lambda zF2 (cong pF (add akT zF2) ZeroC), srT, larT)
                          (oeq_sym_U OF [larEq]) congX0;   (* cong p (a*k + lar) 0 *)
      in congLar0b end;
    val res = recover_p_r_U (rT, pF) rltp goalC cont;
  in res end;
val () = out "STAGE_SC_LARVALUE_READY\n";

(* ============================================================================
   prod_split_sign_cnt : the STRENGTHENED prod_split_sign carrying the count.
     prime2 p ==> ~(p|a) ==> oeq(sub p 1)(add m m) ==>
       Ex S. cong p (LHSp m)(mult S (RHSp m))
             /\ isSign p S
             /\ cong p S (pow (sub p 1)(cnt (flipAbs a p) m))
   ============================================================================ *)
val prod_split_sign_cnt =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val mF = Free("m", natT);
    val hPrime = Thm.assume (ctermU (jT (prime2 pF)));
    val hNa    = Thm.assume (ctermU (jT (neg (dvd pF aF))));
    val hOdd   = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val Laxk = mkAxk aF;          (* mult a *)
    val Llar = mkLar aF pF;       (* lar a p *)
    val flP  = flipAbsU aF pF;    (* %k. lt p (2*rmod(a*k)p) *)
    fun LHSp n = lprod (lmap Laxk (uptoF n));
    fun RHSp n = lprod (lmap Llar (uptoF n));
    val pm1 = sub pF oneC;
    val hpos = lt0_of_prime_U pF hPrime;   (* lt 0 p *)
    fun ExBody n S = mkConj (mkConj (cong pF (LHSp n) (mult S (RHSp n))) (isSign pF S))
                            (cong pF S (pow pm1 (cnt flP n)));
    val sFresh = Free("S_scfresh", natT);
    fun ExAbs n = Term.lambda sFresh (ExBody n sFresh);
    fun goalEx n = mkEx (ExAbs n);
    fun Qbody n = mkImp (le n mF) (goalEx n);
    val nVar = Free("n_sc", natT);
    val Pabs = Term.lambda nVar (Qbody nVar);

    (* ---- base : n = 0 ---- *)
    val base =
      let
        val hle = Thm.assume (ctermU (jT (le ZeroC mF)));
        val u0 = uptoZero_U ();
        fun lp_uptoF0_eq1 fF =
          let
            val lm0 = leq_rw_U (Term.lambda (Free("z_b0", natlistT))
                          (oeq (lprod (lmap fF (uptoF ZeroC))) (lprod (lmap fF (Bound 0)))),
                          uptoF ZeroC, lnilC) u0 (oeqRefl_U (lprod (lmap fF (uptoF ZeroC))));
            val lmnil = lmapNil_U fF;
            val lpc = lprod_cong_U (lmap fF lnilC, lnilC) lmnil;
            val lpnil = lprodNil_U ();
          in oeq_trans_U OF [oeq_trans_U OF [lm0, lpc], lpnil] end;
        val lhs0_1 = lp_uptoF0_eq1 Laxk;    (* LHSp 0 = 1 *)
        val rhs0_1 = lp_uptoF0_eq1 Llar;    (* RHSp 0 = 1 *)
        val cr = cong_refl_U_at (pF, oneC);  (* cong p 1 1 *)
        val m1r = mult1l_U (RHSp ZeroC);          (* (1 * RHSp 0) = RHSp 0 *)
        val m1r_1 = oeq_trans_U OF [m1r, rhs0_1]; (* (1 * RHSp 0) = 1 *)
        val cr2 = cong_rwR_U pF oneC (oneC, mult oneC (RHSp ZeroC)) (oeq_sym_U OF [m1r_1]) cr;
                   (* cong p 1 (mult 1 (RHSp 0)) *)
        val cr3 = cong_rwL_U pF (mult oneC (RHSp ZeroC)) (oneC, LHSp ZeroC) (oeq_sym_U OF [lhs0_1]) cr2;
                   (* cong p (LHSp 0)(mult 1 (RHSp 0)) *)
        val sgn1 = sign_one_U pF;                     (* isSign p 1 *)
        (* count conjunct : cong p 1 (pow pm1 (cnt flP 0)) ; cnt flP 0 = 0 ; pow pm1 0 = 1 *)
        val c0  = cnt0_U flP;                          (* cnt flP 0 = 0 *)
        val pz0 = powZero_U pm1;                       (* pow pm1 0 = 1 *)
        val crS = cong_refl_U_at (pF, oneC);          (* cong p 1 1 *)
        (* rewrite 2nd arg 1 -> pow pm1 0 -> pow pm1 (cnt flP 0) *)
        val cnt_rw = cong_rwR_U pF oneC (oneC, pow pm1 ZeroC) (oeq_sym_U OF [pz0]) crS;  (* cong p 1 (pow pm1 0) *)
        val zcc = Free("z_b0cnt", natT);
        val cntC1 = oeq_rw_U (Term.lambda zcc (cong pF oneC (pow pm1 zcc)), ZeroC, cnt flP ZeroC)
                      (oeq_sym_U OF [c0]) cnt_rw;     (* cong p 1 (pow pm1 (cnt flP 0)) *)
        val conj = conjI_U_at (cong pF (LHSp ZeroC)(mult oneC (RHSp ZeroC)), isSign pF oneC) cr3 sgn1;
        val conj2 = conjI_U_at (mkConj (cong pF (LHSp ZeroC)(mult oneC (RHSp ZeroC)))(isSign pF oneC),
                                cong pF oneC (pow pm1 (cnt flP ZeroC))) conj cntC1;
        val exq = exI_U_at (ExAbs ZeroC, oneC) conj2;
      in impI_U_at (le ZeroC mF, goalEx ZeroC)
           (Thm.implies_intr (ctermU (jT (le ZeroC mF))) exq) end;

    (* ---- step ---- *)
    val stepF =
      let
        val xn = Free("x_sc", natT);
        val IH = Thm.assume (ctermU (jT (Qbody xn)));
        val Sn = suc xn;
        val k = Sn;
        val ak = mult aF k;
        val lark = lar aF pF k;
        val rk  = rOfU aF pF k;              (* rmod(a*k)p *)
        val hleSn = Thm.assume (ctermU (jT (le Sn mF)));
        val lex_sx = le_self_suc_U xn;
        val lexm = le_trans_U_at (xn, Sn, mF) lex_sx hleSn;   (* le x m *)
        val exTail = mp_U_at (le xn mF, goalEx xn) IH lexm;   (* Ex S. ExBody x S *)
        (* LHSp(Suc x) = (a*k) * LHSp x ; RHSp(Suc x) = lark * RHSp x *)
        fun consEq (fF, fk) =
          let
            val us = uptoSuc_U xn;
            val l0 = leq_rw_U (Term.lambda (Free("z_ce", natlistT))
                        (oeq (lprod (lmap fF (uptoF Sn))) (lprod (lmap fF (Bound 0)))),
                        uptoF Sn, lcons Sn (uptoF xn)) us (oeqRefl_U (lprod (lmap fF (uptoF Sn))));
            val lmc = lmapCons_U (fF, Sn, uptoF xn);
            val lmc_b = beta_norm lmc;
            val lpc = lprod_cong_U (lmap fF (lcons Sn (uptoF xn)), lcons fk (lmap fF (uptoF xn))) lmc_b;
            val l1 = oeq_trans_U OF [l0, lpc];
            val lpcons = lprodCons_U (fk, lmap fF (uptoF xn));
          in oeq_trans_U OF [l1, lpcons] end;
        val lhsSucEq = consEq (Laxk, ak);
        val rhsSucEq = consEq (Llar, lark);

        (* core assemble : given tail (St, hCongT, hSignT, hCntT) and per-element
           (sk, perElemCong, sgnSk, hCntStep : cong p (mult sk St)(pow pm1 (cnt flP (Suc x)))),
           build ExBody (Suc x)(mult sk St). *)
        fun assemble (St, hCongT, hSignT) (sk, perElemCong, sgnSk, hCntNew) =
          let
            val cmul = cong_mult_U_at (pF, ak, mult sk lark, LHSp xn, mult St (RHSp xn)) perElemCong hCongT;
            val swap = mult4_swap_U (sk, lark, St, RHSp xn);
            val cmul2 = cong_rwR_U pF (mult ak (LHSp xn))
                          (mult (mult sk lark)(mult St (RHSp xn)), mult (mult sk St)(mult lark (RHSp xn))) swap cmul;
            val cmul3 = cong_rwL_U pF (mult (mult sk St)(mult lark (RHSp xn)))
                          (mult ak (LHSp xn), LHSp Sn) (oeq_sym_U OF [lhsSucEq]) cmul2;
            val cmul4 = let val zc = Free("z_asmU", natT)
                        in oeq_rw_U (Term.lambda zc (cong pF (LHSp Sn) (mult (mult sk St) zc)),
                             mult lark (RHSp xn), RHSp Sn) (oeq_sym_U OF [rhsSucEq]) cmul3 end;
            val Snew = mult sk St;
            val sgnNew = sign_close_U pF sk St hPrime sgnSk hSignT;  (* isSign p (sk*St) *)
            val conj = conjI_U_at (cong pF (LHSp Sn)(mult Snew (RHSp Sn)), isSign pF Snew) cmul4 sgnNew;
            val conj2 = conjI_U_at (mkConj (cong pF (LHSp Sn)(mult Snew (RHSp Sn)))(isSign pF Snew),
                                    cong pF Snew (pow pm1 (cnt flP Sn))) conj hCntNew;
          in exI_U_at (ExAbs Sn, Snew) conj2 end;

        (* per-element : lower branch (sk=1, no flip), upper branch (sk=p-1, flip) *)
        fun lowerBranch (St, hCongT, hSignT, hCntT) hle =   (* hle : le (2 rk) p *)
          let
            val hLoVal = lar_value_lower_U (aF, pF, k) hpos hle;  (* cong p (a*k)(lar) *)
            val m1 = mult1l_U lark;                   (* (1*lark) = lark *)
            val perElem = cong_rwR_U pF ak (lark, mult oneC lark) (oeq_sym_U OF [m1]) hLoVal;
                          (* cong p (a*k)(mult 1 lark) *)
            val sgn1 = sign_one_U pF;
            (* ~flipPred(Suc x) : flipPred = lt p (2 rk) ; from le (2 rk) p, lt p (2 rk) -> le (Suc p)(2 rk),
               le_trans (Suc p)(2 rk) p -> le (Suc p) p = lt p p -> contra (lt_irrefl) *)
            val notFlip =
              let
                val hflip = Thm.assume (ctermU (jT (flipPredU aF pF k)));  (* lt p (2 rk) = le (Suc p)(2 rk) *)
                val le_Sp_p = le_trans_U_at (suc pF, add rk rk, pF) hflip hle;  (* le (Suc p) p = lt p p *)
                val ff = lt_irrefl_U_at pF le_Sp_p;   (* oFalse *)
              in impI_U_at (flipPredU aF pF k, oFalseC)
                   (Thm.implies_intr (ctermU (jT (flipPredU aF pF k))) ff) end;
            val cntStep = cntSucF_U (flP, xn) notFlip;   (* cnt flP (Suc x) = cnt flP x *)
            (* count conjunct for Snew = 1 * St : cong p (mult 1 St)(pow pm1 (cnt flP (Suc x)))
               mult 1 St == St [mult1l] ; cong p St (pow pm1 (cnt flP x)) [hCntT] ;
               pow pm1 (cnt flP x) -> pow pm1 (cnt flP (Suc x)) [cntStep sym, no change to pow]
               So : cong p (1*St) St [cong_of_oeq mult1l], trans hCntT -> cong p (1*St)(pow pm1 (cnt flP x)),
                    then rewrite 2nd arg (cnt flP x)->(cnt flP (Suc x)) via cntStep sym. *)
            val m1St = mult1l_U St;                    (* (1*St) = St *)
            val cong_1St_St = cong_of_oeq_U pF (mult oneC St, St) m1St;   (* cong p (1*St) St *)
            val cong_1St_cnt = cong_trans_U_at (pF, mult oneC St, St, pow pm1 (cnt flP xn)) cong_1St_St hCntT;
                               (* cong p (1*St)(pow pm1 (cnt flP x)) *)
            val zcs = Free("z_lbcnt", natT);
            val hCntNew = oeq_rw_U (Term.lambda zcs (cong pF (mult oneC St)(pow pm1 zcs)),
                            cnt flP xn, cnt flP Sn) (oeq_sym_U OF [cntStep]) cong_1St_cnt;
                          (* cong p (1*St)(pow pm1 (cnt flP (Suc x))) *)
          in assemble (St, hCongT, hSignT) (oneC, perElem, sgn1, hCntNew) end;

        fun upperBranch (St, hCongT, hSignT, hCntT) hlt =   (* hlt : lt p (2 rk) *)
          let
            val hHiVal = lar_value_upper_U (aF, pF, k) hpos hlt;  (* cong p (a*k + lark) 0 *)
            (* perElem cong p (a*k)((p-1)*lark) : same as prod_split_sign upper *)
            val nom = neg_one_mult_U pF lark hPrime;     (* cong p (lark + (p-1)*lark) 0 *)
            val comm = addcomm_U (lark, mult pm1 lark);  (* (lark + pm1*lark)=(pm1*lark + lark) *)
            val nom2 = let val zc = Free("z_ubU", natT)
                       in oeq_rw_U (Term.lambda zc (cong pF zc ZeroC), add lark (mult pm1 lark), add (mult pm1 lark) lark) comm nom end;
                       (* cong p (pm1*lark + lark) 0 *)
            val sym2 = cong_sym_U_at (pF, add (mult pm1 lark) lark, ZeroC) nom2;  (* cong p 0 (pm1*lark + lark) *)
            val both = cong_trans_U_at (pF, add ak lark, ZeroC, add (mult pm1 lark) lark) hHiVal sym2;
                       (* cong p (a*k + lark)(pm1*lark + lark) *)
            val perElem = cong_add_cancel_r_U pF ak (mult pm1 lark) lark both;  (* cong p (a*k)(pm1*lark) *)
            val sgnpm1 = sign_pm1_U pF;
            (* flipPred(Suc x) IS hlt ; cnt increments *)
            val cntStep = cntSucT_U (flP, xn) hlt;   (* cnt flP (Suc x) = Suc(cnt flP x) *)
            (* count conjunct for Snew = (p-1)*St : cong p ((p-1)*St)(pow pm1 (cnt flP (Suc x)))
               cong p ((p-1)*St)((p-1)*(pow pm1 (cnt flP x))) [cong_mult refl pm1, hCntT]
               (p-1)*(pow pm1 (cnt flP x)) = pow pm1 (Suc(cnt flP x)) [pow_Suc sym]
               = pow pm1 (cnt flP (Suc x)) [cntStep sym] *)
            val crpm1 = cong_refl_U_at (pF, pm1);
            val cm = cong_mult_U_at (pF, pm1, pm1, St, pow pm1 (cnt flP xn)) crpm1 hCntT;
                     (* cong p ((p-1)*St)((p-1)*(pow pm1 (cnt flP x))) *)
            val psuc = powSuc_U (pm1, cnt flP xn);  (* pow pm1 (Suc(cnt flP x)) = (p-1)*(pow pm1 (cnt flP x)) *)
            (* rewrite 2nd arg (p-1)*(pow..) -> pow pm1 (Suc(cnt flP x)) via psuc sym *)
            val cm1 = cong_rwR_U pF (mult pm1 St)
                        (mult pm1 (pow pm1 (cnt flP xn)), pow pm1 (suc (cnt flP xn))) (oeq_sym_U OF [psuc]) cm;
                      (* cong p ((p-1)*St)(pow pm1 (Suc(cnt flP x))) *)
            val zcs = Free("z_ubcnt", natT);
            val hCntNew = oeq_rw_U (Term.lambda zcs (cong pF (mult pm1 St)(pow pm1 zcs)),
                            suc (cnt flP xn), cnt flP Sn) (oeq_sym_U OF [cntStep]) cm1;
                          (* cong p ((p-1)*St)(pow pm1 (cnt flP (Suc x))) *)
          in assemble (St, hCongT, hSignT) (pm1, perElem, sgnpm1, hCntNew) end;

        (* tail exE then trichotomy disjE *)
        fun tailBody St hConjT =   (* hConjT : ExBody x St *)
          let
            val cong12 = conjunct1_U_at (mkConj (cong pF (LHSp xn)(mult St (RHSp xn)))(isSign pF St),
                                         cong pF St (pow pm1 (cnt flP xn))) hConjT;
            val hCntT  = conjunct2_U_at (mkConj (cong pF (LHSp xn)(mult St (RHSp xn)))(isSign pF St),
                                         cong pF St (pow pm1 (cnt flP xn))) hConjT;
            val hCongT = conjunct1_U_at (cong pF (LHSp xn)(mult St (RHSp xn)), isSign pF St) cong12;
            val hSignT = conjunct2_U_at (cong pF (LHSp xn)(mult St (RHSp xn)), isSign pF St) cong12;
            val tri = le_or_lt_U (add rk rk, pF);   (* Disj (le (2 rk) p)(lt p (2 rk)) *)
            val cLo = let val h = Thm.assume (ctermU (jT (le (add rk rk) pF)))
                      in Thm.implies_intr (ctermU (jT (le (add rk rk) pF))) (lowerBranch (St, hCongT, hSignT, hCntT) h) end;
            val cHi = let val h = Thm.assume (ctermU (jT (lt pF (add rk rk))))
                      in Thm.implies_intr (ctermU (jT (lt pF (add rk rk)))) (upperBranch (St, hCongT, hSignT, hCntT) h) end;
          in disjE_U_at (le (add rk rk) pF, lt pF (add rk rk), goalEx Sn) tri cLo cHi end;
        val exStep = exE_U_at (ExAbs xn, goalEx Sn) exTail "St_sc" tailBody;
        val imp = impI_U_at (le Sn mF, goalEx Sn) (Thm.implies_intr (ctermU (jT (le Sn mF))) exStep);
        val metaStep = Thm.implies_intr (ctermU (jT (Qbody xn))) imp;
      in Thm.forall_intr (ctermU xn) metaStep end;

    val Qm = nat_induct_U_run Pabs mF base stepF;       (* le m m ==> goalEx m *)
    val lemm = le_refl_U_at mF;                          (* le m m *)
    val res = mp_U_at (le mF mF, goalEx mF) Qm lemm;     (* goalEx m *)
    val d3 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC)(add mF mF)))) res;
    val d2 = Thm.implies_intr (ctermU (jT (neg (dvd pF aF)))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "STAGE_SC_PSC_RAW\n";

(* ---- chain to a^m via the m! cancellation (mirror gauss_lemma) ---- *)
val prod_axk_eq_pow_U   = varifyU prod_axk_eq_pow;
val prod_uptoF_not_dvd_U= varifyU prod_uptoF_not_dvd;
val lar_perm_U          = varifyU lar_perm;

val gauss_sign_count =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val mF = Free("m", natT);
    val hPrime = Thm.assume (ctermU (jT (prime2 pF)));
    val hNa    = Thm.assume (ctermU (jT (neg (dvd pF aF))));
    val hOdd   = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val Laxk = mkAxk aF; val Llar = mkLar aF pF; val flP = flipAbsU aF pF;
    val LprodAxk = lprod (lmap Laxk (uptoF mF));
    val LprodLar = lprod (lmap Llar (uptoF mF));
    val Mfac     = lprod (uptoF mF);
    val powam    = pow aF mF;
    val pm1      = sub pF oneC;
    val muT      = cnt flP mF;
    val goalC    = cong pF powam (pow pm1 muT);

    (* S1 : oeq LprodAxk (mult powam Mfac) *)
    val s1 = beta_norm (Drule.infer_instantiate ctxtU
               [(("a",0), ctermU aF), (("m",0), ctermU mF)] prod_axk_eq_pow_U);
    (* HELP : ~(dvd p Mfac) *)
    val help0 = beta_norm (Drule.infer_instantiate ctxtU
                  [(("p",0), ctermU pF), (("m",0), ctermU mF)] prod_uptoF_not_dvd_U);
    val hNdvdMfac = Thm.implies_elim (Thm.implies_elim help0 hPrime) hOdd;
    (* lar_perm : oeq LprodLar Mfac *)
    val lp0 = beta_norm (Drule.infer_instantiate ctxtU
                [(("p",0), ctermU pF), (("a",0), ctermU aF), (("m",0), ctermU mF)] lar_perm_U);
    val larPermEq = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim lp0 hPrime) hNa) hOdd;
    (* prod_split_sign_cnt : Ex S. cong p LprodAxk (mult S LprodLar) /\ isSign p S /\ cong p S (pow pm1 mu) *)
    val sc0 = beta_norm (Drule.infer_instantiate ctxtU
                [(("p",0), ctermU pF), (("a",0), ctermU aF), (("m",0), ctermU mF)] (toU prod_split_sign_cnt));
    val scEx = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim sc0 hPrime) hNa) hOdd;

    val sFresh = Free("S_scfresh", natT);
    val scAbs = Term.lambda sFresh (mkConj (mkConj (cong pF LprodAxk (mult sFresh LprodLar)) (isSign pF sFresh))
                                           (cong pF sFresh (pow pm1 muT)));

    fun bodyG St hConjT =
      let
        val cong12 = conjunct1_U_at (mkConj (cong pF LprodAxk (mult St LprodLar))(isSign pF St),
                                     cong pF St (pow pm1 muT)) hConjT;
        val hCnt   = conjunct2_U_at (mkConj (cong pF LprodAxk (mult St LprodLar))(isSign pF St),
                                     cong pF St (pow pm1 muT)) hConjT;
        val hCong  = conjunct1_U_at (cong pF LprodAxk (mult St LprodLar), isSign pF St) cong12;
        (* rewrite LprodLar -> Mfac in (mult St LprodLar) *)
        val mcr = mult_cong_r_U (St, LprodLar, Mfac) larPermEq;
        val hCong1 = cong_rwR_U pF LprodAxk (mult St LprodLar, mult St Mfac) mcr hCong;
        (* rewrite LprodAxk -> (powam*Mfac) on LHS *)
        val hCong2 = cong_rwL_U pF (mult St Mfac) (LprodAxk, mult powam Mfac) s1 hCong1;
        (* commute both : (powam*Mfac)->(Mfac*powam), (St*Mfac)->(Mfac*St) *)
        val cL = multcomm_U (powam, Mfac);
        val cR = multcomm_U (St, Mfac);
        val hCong3 = cong_rwL_U pF (mult St Mfac) (mult powam Mfac, mult Mfac powam) cL hCong2;
        val hCong4 = cong_rwR_U pF (mult Mfac powam) (mult St Mfac, mult Mfac St) cR hCong3;
        (* mod_cancel : cong p powam St *)
        val cancelled = mod_cancel_U_at (pF, Mfac, powam, St) hPrime hNdvdMfac hCong4;  (* cong p powam St *)
        (* chain cong p powam St (cancelled) + cong p St (pow pm1 mu) (hCnt) -> cong p powam (pow pm1 mu) *)
        val res = cong_trans_U_at (pF, powam, St, pow pm1 muT) cancelled hCnt;
      in res end;

    val exG = exE_U_at (scAbs, goalC) scEx "S_scw" bodyG;   (* goalC *)
    val d3 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC)(add mF mF)))) exG;
    val d2 = Thm.implies_intr (ctermU (jT (neg (dvd pF aF)))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "STAGE_SC_RAW\n";

(* validate SC *)
val pV_sc = Var(("p",0),natT); val aV_sc = Var(("a",0),natT); val mV_sc = Var(("m",0),natT);
val flPv_sc = flipAbsU aV_sc pV_sc;
val i_gauss_sign_count =
  Logic.mk_implies (jT (prime2 pV_sc),
    Logic.mk_implies (jT (neg (dvd pV_sc aV_sc)),
      Logic.mk_implies (jT (oeq (sub pV_sc oneC)(add mV_sc mV_sc)),
        jT (cong pV_sc (pow aV_sc mV_sc) (pow (sub pV_sc oneC) (cnt flPv_sc mV_sc))))));
val r_gauss_sign_count = checkF2c ("gauss_sign_count", gauss_sign_count, i_gauss_sign_count);
(* soundness probes : dropping ~(p|a) or oddness must change the statement *)
val probe_sc_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (prime2 pV_sc),
        Logic.mk_implies (jT (oeq (sub pV_sc oneC)(add mV_sc mV_sc)),
          jT (cong pV_sc (pow aV_sc mV_sc) (pow (sub pV_sc oneC) (cnt flPv_sc mV_sc)))))
  in not ((Thm.prop_of gauss_sign_count) aconv bogus) end;
val probe_sc_needs_odd =
  let val bogus = Logic.mk_implies (jT (prime2 pV_sc),
        Logic.mk_implies (jT (neg (dvd pV_sc aV_sc)),
          jT (cong pV_sc (pow aV_sc mV_sc) (pow (sub pV_sc oneC) (cnt flPv_sc mV_sc)))))
  in not ((Thm.prop_of gauss_sign_count) aconv bogus) end;
val () = if probe_sc_needs_ndvd then out "PROBE_OK gauss_sign_count keeps ~(p|a)\n" else out "PROBE_FAIL sc ndvd\n";
val () = if probe_sc_needs_odd then out "PROBE_OK gauss_sign_count keeps oddness\n" else out "PROBE_FAIL sc odd\n";
fun gauss_sign_count_at (pt, at, mt) hPrime hNa hOdd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("m",0), ctermU mt)] (toU gauss_sign_count))
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) hNa) hOdd end;
val () = if r_gauss_sign_count andalso probe_sc_needs_ndvd andalso probe_sc_needs_odd
         then out "GAUSS_SIGN_COUNT_OK\n" else out "GAUSS_SIGN_COUNT_FAILED\n";
val () = out "STAGE_SC_END\n";

(* ############################################################################
   ##########  (EL)  EISENSTEIN LEMMA  ########################################
   prime2 p ==> parity p = 1 ==> prime2 q ==> parity q = 1 ==> ~(p|q) ==> (p-1=m+m)
     ==> cong p (pow q m) (pow (sub p 1) (sumf (\k. rdiv (mult q k) p) m))
   [ q^m == (p-1)^(sum_{k=1..m} floor(q*k/p)) mod p ;  the Eisenstein lemma.
     (the parity q = 1 premise -- q ODD -- is what eisenstein_parity genuinely
      needs; it holds for the odd primes q of quadratic reciprocity.) ]
   Chain (mu := cnt flipPred m,  FL := sumf floor m) :
     q^m == (p-1)^mu              [gauss_sign_count, a:=q]
         == (p-1)^(parity mu)     [pow_neg1_mod]
         =  (p-1)^(parity FL)     [eisenstein_parity : parity mu = parity FL, exponent oeq]
         == (p-1)^FL              [pow_neg1_mod backwards]
   ############################################################################ *)
val () = out "STAGE_EL_BEGIN\n";
val eisenstein_parity_U = eisenstein_parity;   (* already on ctxtU *)
val eisenstein_lemma =
  let
    val pF = Free("p", natT); val qF = Free("q", natT); val mF = Free("m", natT);
    val hPrimeP = Thm.assume (ctermU (jT (prime2 pF)));
    val hoddP   = Thm.assume (ctermU (jT (oeq (parity pF) oneC)));
    val hPrimeQ = Thm.assume (ctermU (jT (prime2 qF)));
    val hoddQ   = Thm.assume (ctermU (jT (oeq (parity qF) oneC)));
    val hNq     = Thm.assume (ctermU (jT (neg (dvd pF qF))));
    val hOdd    = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val pm1 = sub pF oneC;
    val flP = flipAbsU qF pF;   val flA = floorAbsU qF pF;
    val muT = cnt flP mF;       val FL = sumf flA mF;
    val hpos = lt0_of_prime_U pF hPrimeP;   (* lt 0 p *)

    (* SC at a:=q : cong p (pow q m)(pow pm1 mu) *)
    val scE = gauss_sign_count_at (pF, qF, mF) hPrimeP hNq hOdd;  (* cong p (pow q m)(pow pm1 mu) *)
    (* PN at k:=mu : cong p (pow pm1 mu)(pow pm1 (parity mu)) *)
    val pnMu = pow_neg1_mod_at (pF, muT) hPrimeP;   (* cong p (pow pm1 mu)(pow pm1 (parity mu)) *)
    (* eisenstein_parity : parity mu = parity FL *)
    val epI = beta_norm (Drule.infer_instantiate ctxtU
                [(("q",0), ctermU qF),(("p",0), ctermU pF),(("m",0), ctermU mF)] eisenstein_parity_U);
    val epE = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
                (Thm.implies_elim (Thm.implies_elim epI hpos) hoddQ) hoddP) hPrimeP) hNq) hOdd;
              (* oeq (parity mu)(parity FL) *)
    (* pow pm1 (parity mu) = pow pm1 (parity FL) : oeq exponent rewrite ; lift to cong *)
    val zcE = Free("z_elexp", natT);
    val powExpEq = oeq_rw_U (Term.lambda zcE (oeq (pow pm1 (parity muT)) (pow pm1 zcE)),
                     parity muT, parity FL) epE (oeqRefl_U (pow pm1 (parity muT)));
                   (* oeq (pow pm1 (parity mu))(pow pm1 (parity FL)) *)
    val congPowExp = cong_of_oeq_U pF (pow pm1 (parity muT), pow pm1 (parity FL)) powExpEq;
                     (* cong p (pow pm1 (parity mu))(pow pm1 (parity FL)) *)
    (* PN at k:=FL : cong p (pow pm1 FL)(pow pm1 (parity FL)) ; sym -> cong p (pow pm1 (parity FL))(pow pm1 FL) *)
    val pnFL = pow_neg1_mod_at (pF, FL) hPrimeP;   (* cong p (pow pm1 FL)(pow pm1 (parity FL)) *)
    val pnFLsym = cong_sym_U_at (pF, pow pm1 FL, pow pm1 (parity FL)) pnFL;  (* cong p (pow pm1 (parity FL))(pow pm1 FL) *)
    (* assemble : cong p (pow q m)(pow pm1 FL) by 4-step transitivity *)
    val t1 = cong_trans_U_at (pF, pow qF mF, pow pm1 muT, pow pm1 (parity muT)) scE pnMu;
             (* cong p (pow q m)(pow pm1 (parity mu)) *)
    val t2 = cong_trans_U_at (pF, pow qF mF, pow pm1 (parity muT), pow pm1 (parity FL)) t1 congPowExp;
             (* cong p (pow q m)(pow pm1 (parity FL)) *)
    val t3 = cong_trans_U_at (pF, pow qF mF, pow pm1 (parity FL), pow pm1 FL) t2 pnFLsym;
             (* cong p (pow q m)(pow pm1 FL) *)
    val d6 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC)(add mF mF)))) t3;
    val d5 = Thm.implies_intr (ctermU (jT (neg (dvd pF qF)))) d6;
    val d4 = Thm.implies_intr (ctermU (jT (oeq (parity qF) oneC))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (prime2 qF))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (oeq (parity pF) oneC))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val () = out "STAGE_EL_RAW\n";

(* validate EL *)
val pV_el = Var(("p",0),natT); val qV_el = Var(("q",0),natT); val mV_el = Var(("m",0),natT);
val flAv_el = floorAbsU qV_el pV_el;
val i_eisenstein_lemma =
  Logic.mk_implies (jT (prime2 pV_el),
    Logic.mk_implies (jT (oeq (parity pV_el) oneC),
      Logic.mk_implies (jT (prime2 qV_el),
        Logic.mk_implies (jT (oeq (parity qV_el) oneC),
          Logic.mk_implies (jT (neg (dvd pV_el qV_el)),
            Logic.mk_implies (jT (oeq (sub pV_el oneC)(add mV_el mV_el)),
              jT (cong pV_el (pow qV_el mV_el)
                      (pow (sub pV_el oneC) (sumf flAv_el mV_el)))))))));
val r_eisenstein_lemma = checkF2c ("eisenstein_lemma", eisenstein_lemma, i_eisenstein_lemma);
(* soundness probes : dropping ~(p|q) or oddness of q must change the statement *)
val probe_el_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (prime2 pV_el),
        Logic.mk_implies (jT (oeq (parity pV_el) oneC),
          Logic.mk_implies (jT (prime2 qV_el),
            Logic.mk_implies (jT (oeq (parity qV_el) oneC),
              Logic.mk_implies (jT (oeq (sub pV_el oneC)(add mV_el mV_el)),
                jT (cong pV_el (pow qV_el mV_el)(pow (sub pV_el oneC) (sumf flAv_el mV_el))))))))
  in not ((Thm.prop_of eisenstein_lemma) aconv bogus) end;
val probe_el_needs_oddq =
  let val bogus = Logic.mk_implies (jT (prime2 pV_el),
        Logic.mk_implies (jT (oeq (parity pV_el) oneC),
          Logic.mk_implies (jT (prime2 qV_el),
            Logic.mk_implies (jT (neg (dvd pV_el qV_el)),
              Logic.mk_implies (jT (oeq (sub pV_el oneC)(add mV_el mV_el)),
                jT (cong pV_el (pow qV_el mV_el)(pow (sub pV_el oneC) (sumf flAv_el mV_el))))))))
  in not ((Thm.prop_of eisenstein_lemma) aconv bogus) end;
val () = if probe_el_needs_ndvd then out "PROBE_OK eisenstein_lemma keeps ~(p|q)\n" else out "PROBE_FAIL el ndvd\n";
val () = if probe_el_needs_oddq then out "PROBE_OK eisenstein_lemma keeps parity q = 1\n" else out "PROBE_FAIL el oddq\n";
val eisLemmaFull2 = r_eisenstein_lemma andalso probe_el_needs_ndvd andalso probe_el_needs_oddq;
val () = if eisLemmaFull2 then out "EIS_LEMMA_OK\n" else out "EIS_LEMMA_FAILED\n";
val () = out "STAGE_EL_END\n";

(* ############################################################################
   SOUNDNESS + AXIOM AUDIT (the F2c delta)
   F2c is PURE PROOF over the existing tower : NO new constants, NO new axioms.
   The only classical axiom remains ex_middle ; nothing fabricated.
   ############################################################################ *)
val () = out "F2C_AUDIT_BEGIN\n";
val allAxF2c = Theory.all_axioms_of thyU;
val () = out ("f2c_axiom_count=" ^ Int.toString (length allAxF2c) ^ "\n");
val hasEMc = List.exists (fn (nm,_) => String.isSuffix "ex_middle" nm orelse nm = "ex_middle") allAxF2c;
val () = out ("f2c_ex_middle_present=" ^ Bool.toString hasEMc ^ "\n");
(* F2c must add NO new axiom : count must equal the F2b count (84). enumerate any
   gauss/eisenstein/sign/count/legendre/reciprocity-named axiom (should be NONE). *)
val badC = List.filter (fn nm => let val l = String.map Char.toLower nm in
              String.isSubstring "eisenstein" l orelse String.isSubstring "legendre" l
              orelse String.isSubstring "reciprocity" l orelse String.isSubstring "sign_count" l
              orelse String.isSubstring "gauss" l orelse String.isSubstring "flip" l
              orelse String.isSubstring "pow_neg1" l orelse String.isSubstring "pm1_sq" l end)
            (map fst allAxF2c);
val () = out ("f2c_fabricated_axioms=[" ^ String.concatWith "," badC ^ "]\n");
val () = out "F2C_AUDIT_END\n";

(* ---- master gate ---- *)
val f2cAllOK = r_pow_neg1_mod andalso probe_pn_needs_prime
               andalso r_gauss_sign_count andalso probe_sc_needs_ndvd andalso probe_sc_needs_odd
               andalso eisLemmaFull2
               andalso hasEMc andalso (badC = []);
val () = if f2cAllOK then out "QR_F2C_ALL_OK\n" else out "QR_F2C_PARTIAL\n";
val () = out ("F2C_SUMMARY gaussSignCountProved=" ^ Bool.toString r_gauss_sign_count
              ^ " powNeg1ModProved=" ^ Bool.toString r_pow_neg1_mod
              ^ " eisensteinLemmaProved=" ^ Bool.toString eisLemmaFull2 ^ "\n");
(* enumerate ALL axiom names for the audit line (only ex_middle classical) *)
val () = out "F2C_AXIOM_ENUM_BEGIN\n";
val () = List.app (fn (nm,_) => out ("  axiom: " ^ nm ^ "\n")) allAxF2c;
val () = out "F2C_AXIOM_ENUM_END\n";
val () = out "F2C_END\n";

