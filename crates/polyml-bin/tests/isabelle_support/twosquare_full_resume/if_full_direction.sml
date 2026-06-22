(* ============================================================================
   FERMAT TWO-SQUARE — THE IF-DIRECTION (assembled), on the twosquare monolith
   final context ctxtGR / ctermGR.

   Appended AFTER:
     isabelle_twosquare.sml  (final ctxtGR; gives prime_divisor_exists,
        strong_induct, prime2, pow, the natlist lib, the full _gr/_r/_g/_d toolkit)
   + if_direction.sml        (sumsqBody, sumsq_mult, two_is_sumsq, sq_is_sumsq,
        prod_all_sumsq, brahma4, ...)
   + tsf_trichotomy.sml      (mod4_trichotomy : prime2 p => p=2 \/ 4k+1 \/ 4k+3)
   + tsf_perprime.sml        (pow2_sumsq, p1mod4_pow_sumsq, p3mod4_even_sumsq)
   + tsf_valuation.sml       (vpredBody, evenBody, fourk3, hpBody, val_transfer,
        padic_split, prime_not_dvd_pow, val_coprime_self, ...)

   GOAL (the if-direction) :
     if_direction : 0 < n ==> H_pred n ==> sumsq n
   where
     H_pred n  ==  hpBody n
               ==  !p. prime2 p ==> (Ex k. p = (((k+k)+k)+k)+3)
                       ==> !e. vpred p n e ==> Ex j. e = j+j
     vpred p n e  ==  Ex m. n = p^e * m  /\  ~(p|m)
     sumsq n      ==  Ex a b. n = a*a + b*b

   PROOF (strong induction on n) :  given 0<n and H_pred n,
     - n=1 : sumsq 1 = 1*1 + 0*0 directly.
     - n>=2: prime_divisor_exists gives a prime2 p with p|n.
             padic_split gives n = p^v*m, ~(p|m).
             p|n + ~p|m forces v>=1 (v=Suc w).  0<m (n=p^v*m>0).  m<n (p^v>=2, m>=1).
             IH at m (via val_transfer : H_pred m) gives sumsq m.
             classify p mod 4 (mod4_trichotomy):
               p=2     -> pow2_sumsq        : sumsq (p^v)
               p=4k+1  -> p1mod4_pow_sumsq  : sumsq (p^v)
               p=4k+3  -> v even (vpred p n v + H_pred n at p,v) -> p3mod4_even_sumsq.
             sumsq(p^v) * sumsq m -> sumsq(p^v*m) = sumsq n  (sumsq_mult).
   0 new axioms / consts / types.  Only classical = ex_middle.
   ============================================================================ *)
val () = out "TSF_IFDIR_BEGIN\n";

(* ---- numerals ---- *)
val z0 = ZeroC; val s1 = suc ZeroC; val s2 = suc (suc ZeroC);
val s3 = suc (suc (suc ZeroC)); val s4 = suc (suc (suc (suc ZeroC)));

(* ---- predicate builders (MUST match the valuation driver's forms exactly so
        val_transfer / padic_split / hpBody apply) ---- *)
(* sumsqBody, vpredBody, vpredEBody, evenBody, fourk3, hpBody already in scope
   from if_blocks.sml + tsf_valuation.sml.  Re-state local aliases for clarity. *)
fun ssBody nT  = sumsqBody nT;       (* Ex a b. n = a*a+b*b *)

(* ---- a few more base lemmas onto ctxtGR ---- *)
val mult_1_right_gr2 = varify mult_1_right;
fun mult1r_gr2 t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_1_right_gr2);

val () = out "TSF_IFDIR_TERMS_OK\n";

(* ===========================================================================
   BRIDGE LEMMAS : the trichotomy emits `add (mult 4 k) r`, but the per-prime
   leaves want `add (fourk k) r` (fourk k = (k+k)+(k+k)) and the H_pred / fourk3
   wants `add (((k+k)+k)+k) r`.  Prove the two 4k-equalities and the
   existential-rewrite that converts a trichotomy disjunct into a consumer form.
   =========================================================================== *)
(* mult4_chain k : oeq (mult 4 k) (((k+k)+k)+k)   [the fourk3 4k-shape] *)
fun mult4_to_fk3 kT =
  let
    (* mult 4 k = mult (Suc(Suc(Suc(Suc 0)))) k
               = add k (mult 3 k)       [mult_Suc]
               = add k (add k (mult 2 k))
               = add k (add k (add k (mult 1 k)))
               = add k (add k (add k (add k (mult 0 k))))
               = add k (add k (add k (add k 0)))
       and (((k+k)+k)+k) is left-nested.  Easier: prove both equal `mult 4 k`?
       Use the semiring directly :  ((k+k)+k)+k  vs  mult 4 k.
       mult 4 k = k + (k + (k + (k + 0)))   (right-nested), then add_assoc/comm to
       reach (((k+k)+k)+k).  We just need oeq (mult 4 k) (((k+k)+k)+k). *)
    val m1 = multSuc_gr (s3, kT);                 (* 4*k = k + 3*k *)
    val m2 = multSuc_gr (s2, kT);                 (* 3*k = k + 2*k *)
    val m3 = multSuc_gr (s1, kT);                 (* 2*k = k + 1*k *)
    val m4 = multSuc_gr (z0, kT);                 (* 1*k = k + 0*k *)
    val m5 = mult0_gr kT;                          (* 0*k = 0 *)
    (* 1*k = k + 0 *)
    val m4b = oeqTrans_gr (m4, add_cong_r_gr (kT, mult z0 kT, z0) m5);   (* 1*k = k+0 *)
    val m4c = oeqTrans_gr (m4b, add0r_gr kT);      (* need add0r_gr : add k 0 = k *)
    (* 2*k = k + (k+0) = k + k *)
    val m3b = oeqTrans_gr (m3, add_cong_r_gr (kT, mult s1 kT, kT) m4c);  (* 2*k = k + k *)
    (* 3*k = k + (k+k) *)
    val m2b = oeqTrans_gr (m2, add_cong_r_gr (kT, mult s2 kT, add kT kT) m3b);  (* 3*k = k+(k+k) *)
    (* 4*k = k + (k+(k+k)) *)
    val m1b = oeqTrans_gr (m1, add_cong_r_gr (kT, mult s3 kT, add kT (add kT kT)) m2b);  (* 4*k = k+(k+(k+k)) *)
    (* now re-associate k+(k+(k+k)) = ((k+k)+k)+k via add_assoc *)
    (* k+(k+(k+k)) : let A=k, B=k, C=(k+k) ; add_assoc m n k : (m+n)+k = m+(n+k) ?
       check add_assoc direction below.  We will use add_assoc both ways carefully. *)
    val rhs0 = add kT (add kT (add kT kT));        (* k+(k+(k+k)) *)
    (* step1 : k+(k+(k+k)) = (k+k)+(k+k)  [add_assoc reversed on outer]
       add_assoc (a,b,c) : oeq (add (add a b) c) (add a (add b c))  [(a+b)+c = a+(b+c)]
       so add_assoc(k,k,(k+k)) : (k+k)+(k+k) = k+(k+(k+k)).  sym -> k+(k+(k+k))=(k+k)+(k+k). *)
    val as1 = oeqSym_gr (addassoc_gr (kT, kT, add kT kT));   (* k+(k+(k+k)) = (k+k)+(k+k) *)
    (* step2 : (k+k)+(k+k) = ((k+k)+k)+k  [add_assoc reversed on inner-right]
       add_assoc((k+k),k,k) : ((k+k)+k)+k = (k+k)+(k+k).  sym. *)
    val as2 = oeqSym_gr (addassoc_gr (add kT kT, kT, kT));   (* (k+k)+(k+k) = ((k+k)+k)+k *)
    val chain = oeqTrans_gr (m1b, oeqTrans_gr (as1, as2));   (* 4*k = ((k+k)+k)+k *)
  in chain end;
(* need add0r_gr (add k 0 = k) on ctxtGR *)
val add_0_right_grB = varify add_0_right;
fun add0r_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_right_grB);

(* mult4_to_fk (perprime fourk) : oeq (mult 4 k) ((k+k)+(k+k)) *)
fun mult4_to_fk kT =
  let
    val m1 = multSuc_gr (s3, kT);
    val m2 = multSuc_gr (s2, kT);
    val m3 = multSuc_gr (s1, kT);
    val m4 = multSuc_gr (z0, kT);
    val m5 = mult0_gr kT;
    val m4b = oeqTrans_gr (m4, add_cong_r_gr (kT, mult z0 kT, z0) m5);
    val m4c = oeqTrans_gr (m4b, add0r_gr kT);
    val m3b = oeqTrans_gr (m3, add_cong_r_gr (kT, mult s1 kT, kT) m4c);
    val m2b = oeqTrans_gr (m2, add_cong_r_gr (kT, mult s2 kT, add kT kT) m3b);
    val m1b = oeqTrans_gr (m1, add_cong_r_gr (kT, mult s3 kT, add kT (add kT kT)) m2b);  (* 4*k = k+(k+(k+k)) *)
    (* k+(k+(k+k)) = (k+k)+(k+k) : add_assoc(k,k,(k+k)) sym *)
    val as1 = oeqSym_gr (addassoc_gr (kT, kT, add kT kT));   (* k+(k+(k+k)) = (k+k)+(k+k) *)
    val chain = oeqTrans_gr (m1b, as1);                       (* 4*k = (k+k)+(k+k) *)
  in chain end;

val () = out "TSF_IFDIR_BRIDGES_OK\n";

(* ---- self-test the bridges (Free k) ---- *)
val () =
  let val kk = Free("k_brtest", natT)
      val b3 = mult4_to_fk3 kk
      val bf = mult4_to_fk kk
      val ok3 = (Thm.prop_of b3) aconv (jT (oeq (mult s4 kk) (add (add (add kk kk) kk) kk)))
      val okf = (Thm.prop_of bf) aconv (jT (oeq (mult s4 kk) (add (add kk kk)(add kk kk))))
  in out ("BRIDGE3 aconv="^Bool.toString ok3^" hyps="^Int.toString(length(Thm.hyps_of b3))^"\n");
     out ("BRIDGEF aconv="^Bool.toString okf^" hyps="^Int.toString(length(Thm.hyps_of bf))^"\n") end
  handle e => out ("BRIDGE_TEST_FAIL "^exnMessage e^"\n");

val () = out "TSF_IFDIR_HELPERS_DONE\n";
(* ============================================================================
   THE IF-DIRECTION : strong induction assembly (continuation).
     if_direction : 0 < n ==> hpBody n ==> sumsq n
   ============================================================================ *)
val () = out "TSF_IFDIR_MAIN_BEGIN\n";

(* helpers for v>=1, 0<m, m<n *)
val n1if = suc ZeroC; val n2if = suc (suc ZeroC);

(* lt_m_Km : 0<m ==> le 2 K ==> lt m (mult K m)   (m < K*m when K>=2, m>0)
   m < m+m  [lt_p_2p, needs 0<m i.e. le 1 m]
   m+m = 2*m = m*2 ; m*2 <= m*K  [mult_le_mono_g (m,2,K) on le 2 K] ; m*K = K*m [comm]
   so lt m (m+m) <= le (m+m)(K*m) -> lt m (K*m). *)
fun lt_m_Km (mT, KT) hPosM hle2K =
  let
    val ltm2m = lt_p_2p mT hPosM;                        (* lt m (m+m) = le (Suc m)(m+m) *)
    (* m*2 <= m*K *)
    val lemmono = mult_le_mono_g (mT, n2if, KT) hle2K;   (* le (m*2)(m*K) *)
    (* m*2 = m+m : two_p_eq_d m gives 2*m = m+m ; multcomm m 2 : m*2 = 2*m *)
    val m2eq = oeqTrans_r2 (multcomm_g (mT, n2if), two_p_eq_d mT);  (* m*2 = m+m *)
    (* rewrite le (m*2)(m*K) -> le (m+m)(m*K) *)
    val z1 = Free("zlmk1", natT); val Pl1 = Term.lambda z1 (le z1 (mult mT KT));
    val l1 = oeq_rw_r (Pl1, mult mT n2if, add mT mT) m2eq lemmono;  (* le (m+m)(m*K) *)
    (* rewrite m*K -> K*m *)
    val z2 = Free("zlmk2", natT); val Pl2 = Term.lambda z2 (le (add mT mT) z2);
    val l2 = oeq_rw_r (Pl2, mult mT KT, mult KT mT) (multcomm_g (mT, KT)) l1;  (* le (m+m)(K*m) *)
    (* lt m (K*m) : le_trans (Suc m)(m+m)(K*m) *)
  in le_trans_d (suc mT, add mT mT, mult KT mT) ltm2m l2 end;

(* pow_ge_2 : le 2 p ==> le 2 (pow p (Suc w))   (p^(Suc w) >= p >= 2)
   pow p (Suc w) = p * pow p w >= p * 1 = p >= 2.
   need le 1 (pow p w) [pow positive] -> le (p*1)(p*pow p w) [mult_le_mono] = le p (p * pow p w)
   = le p (pow p (Suc w)) ; combine with le 2 p by le_trans. *)
(* pow_pos : le 1 (pow p w)  (1 <= p^w) for any p>=1.  Induction on w.
   Simpler: from le 2 p we get le 1 p, and p^w >= 1 by induction. Use a dedicated lemma. *)
val pow_pos =
  let
    val pF = Free("p_pp", natT);
    val hLe1P_P = jT (le n1if pF); val hLe1P = Thm.assume (ctermGR hLe1P_P);
    val wF = Free("w_pp", natT);
    val Rabs = Term.lambda wF (le n1if (pow pF wF));
    (* base w=0 : le 1 (pow p 0) = le 1 1 (le_refl) *)
    val base =
      let val pz = powZero_gr pF;                         (* oeq (pow p 0) 1 *)
          val lerefl = le_refl_g n1if;                    (* le 1 1 *)
          val z = Free("zpp0", natT); val Pl = Term.lambda z (le n1if z);
      in oeq_rw_r (Pl, n1if, pow pF ZeroC) (oeqSym_r2 pz) lerefl end;  (* le 1 (pow p 0) *)
    val step =
      let val xF = Free("x_pp", natT);
          val hRxP = jT (le n1if (pow pF xF)); val hRx = Thm.assume (ctermGR hRxP);
          (* pow p (Suc x) = p * pow p x ; >= p*1 = p [mult_le_mono p,1,pow p x] >= 1 *)
          val ps = powSuc_gr (pF, xF);                    (* oeq (pow p (Suc x)) (p * pow p x) *)
          (* le (p*1)(p * pow p x) from le 1 (pow p x) *)
          val lem = mult_le_mono_g (pF, n1if, pow pF xF) hRx;  (* le (p*1)(p*pow p x) *)
          (* p*1 = p *)
          val p1 = mult1r_gr2 pF;                         (* oeq (p*1) p *)
          val z1 = Free("zpps1", natT); val Pl1 = Term.lambda z1 (le z1 (mult pF (pow pF xF)));
          val lemP = oeq_rw_r (Pl1, mult pF n1if, pF) p1 lem;   (* le p (p*pow p x) *)
          (* le 1 p from hLe1P, le_trans 1 p (p*pow p x) *)
          val le1ppx = le_trans_d (n1if, pF, mult pF (pow pF xF)) hLe1P lemP;  (* le 1 (p*pow p x) *)
          (* rewrite (p*pow p x) -> pow p (Suc x) *)
          val z2 = Free("zpps2", natT); val Pl2 = Term.lambda z2 (le n1if z2);
          val res = oeq_rw_r (Pl2, mult pF (pow pF xF), pow pF (suc xF)) (oeqSym_r2 ps) le1ppx;
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR hRxP) res) end;
    val wK = Free("wK_pp", natT);
    val indThm = nat_induct_r Rabs wK base step;          (* le 1 (pow p wK) *)
  in varify (Thm.implies_intr (ctermGR hLe1P_P) indThm) end;
fun pow_pos_at (pT, wT) hLe1 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
     [(("p_pp",0), ctermGR pT),(("wK_pp",0), ctermGR wT)] pow_pos)) hLe1;
val () = out ("pow_pos hyps="^Int.toString(length(Thm.hyps_of pow_pos))^"\n");

(* le1_of_le2 : le 2 p ==> le 1 p   (1<=2<=p)  via le_trans + le_1_2 *)
val le_1_2 =
  let val a1 = add0r_gr n1if  (* add 1 0 = 1 ? need le 1 2 = Ex w. 2 = 1+w, witness 1 *)
      (* 2 = 1 + 1 : add (Suc 0)(Suc 0) = Suc(add 0 (Suc 0)) = Suc(Suc 0) *)
      val aS = addSuc_gr (ZeroC, n1if);                    (* add 1 1 = Suc(add 0 1) *)
      val a0 = add0_gr n1if;                                (* add 0 1 = 1 *)
      val sucA0 = Suc_cong_gr2 a0;                          (* Suc(add 0 1) = Suc 1 = 2 *)
      val a11 = oeqTrans_gr (aS, sucA0);                    (* add 1 1 = 2 *)
      val a11s = oeqSym_gr a11;                             (* 2 = add 1 1 *)
      val Pabs = Term.lambda (Free("w_l12", natT)) (oeq n2if (add n1if (Free("w_l12", natT))));
  in exI_r Pabs n1if a11s end;                              (* le 1 2 *)
fun le1_of_le2 (pT) hLe2 = le_trans_d (n1if, n2if, pT) le_1_2 hLe2;  (* le 1 p *)

(* pow_ge_2 : le 2 p ==> le 2 (pow p (Suc w))   *)
fun pow_ge_2 (pT, wT) hLe2 =
  let
    val hLe1 = le1_of_le2 pT hLe2;                          (* le 1 p *)
    (* le 1 (pow p w) *)
    val lepw = pow_pos_at (pT, wT) hLe1;                    (* le 1 (pow p w) *)
    (* le (p*1)(p * pow p w) *)
    val lem = mult_le_mono_g (pT, n1if, pow pT wT) lepw;    (* le (p*1)(p*pow p w) *)
    val p1 = mult1r_gr2 pT;                                 (* oeq (p*1) p *)
    val z1 = Free("zpg21", natT); val Pl1 = Term.lambda z1 (le z1 (mult pT (pow pT wT)));
    val lemP = oeq_rw_r (Pl1, mult pT n1if, pT) p1 lem;     (* le p (p*pow p w) *)
    (* le 2 (p*pow p w) by le_trans 2 p (p*pow p w) *)
    val le2 = le_trans_d (n2if, pT, mult pT (pow pT wT)) hLe2 lemP;  (* le 2 (p*pow p w) *)
    (* rewrite p*pow p w -> pow p (Suc w) *)
    val ps = powSuc_gr (pT, wT);                            (* oeq (pow p (Suc w))(p*pow p w) *)
    val z2 = Free("zpg22", natT); val Pl2 = Term.lambda z2 (le n2if z2);
  in oeq_rw_r (Pl2, mult pT (pow pT wT), pow pT (suc wT)) (oeqSym_r2 ps) le2 end;

val () = out "TSF_IFDIR_ARITH_OK\n";
(* ============================================================================
   THE IF-DIRECTION STRONG INDUCTION (continuation of tsf_ifdir.sml).
   ============================================================================ *)
val () = out "TSF_IFDIR_SI_BEGIN\n";

(* base lemmas onto ctxtGR needed below *)
val sumsq_one_if =
  let
    val one = suc ZeroC;
    val m11 = mult1l_gr one;                              (* (1*1) = 1 *)
    val zz0 = mult0_gr ZeroC;                             (* (0*0) = 0 *)
    val cong0 = add_cong_r_gr (mult one one, mult ZeroC ZeroC, ZeroC) zz0;
    val ac = addcomm_gr (mult one one, ZeroC);
    val a0 = add0_gr (mult one one);
    val add0r = oeqTrans_gr (ac, a0);
    val rhs1 = oeqTrans_gr (oeqTrans_gr (cong0, add0r), m11);   (* (1*1)+(0*0) = 1 *)
    val rhsSym = oeqSym_gr rhs1;                          (* 1 = (1*1)+(0*0) *)
  in mk_sumsq one (one, ZeroC) rhsSym end;                (* sumsq 1 *)
val () = out ("sumsq_one_if hyps="^Int.toString(length(Thm.hyps_of sumsq_one_if))^"\n");

(* ===========================================================================
   classify_pow_sumsq : given prime2 p (hPp), and (vpred p n v) holding (so the
   exponent v has an even-valuation guarantee from H when p=4k+3), produce
   sumsq (pow p v).  Inputs:
     pT, vT, nT   : terms (p, v, n)
     hPp          : jT (prime2 p)
     hH           : jT (hpBody n)   (the per-prime even hypothesis at n)
     hVpv         : jT (vpredBody (p, n, v))   (vpred p n v : Ex m. n=p^v*m /\ ~p|m)
   Output: jT (sumsqBody (pow p v)).
   =========================================================================== *)
fun classify_pow_sumsq (pT, vT, nT) hPp hH hVpv =
  let
    val tri = (varify mod4_trichotomy);    (* schematic p_tri *)
    val triAt = beta_norm (Drule.infer_instantiate ctxtGR [(("p_tri",0), ctermGR pT)] tri);
    val triDisj = Thm.implies_elim triAt hPp;   (* Disj (p=2)(Disj (4k+1)(4k+3)) *)
    val n1 = suc ZeroC; val n2 = suc (suc ZeroC); val n3 = suc (suc (suc ZeroC));
    val n4 = suc (suc (suc (suc ZeroC)));
    (* the three disjunct body terms, as in the trichotomy *)
    val Aterm   = oeq pT n2;
    val midEx   = mkEx (Term.lambda (Free("k_m", natT)) (oeq pT (add (mult n4 (Free("k_m", natT))) n1)));
    val rightEx = mkEx (Term.lambda (Free("k_r", natT)) (oeq pT (add (mult n4 (Free("k_r", natT))) n3)));
    val innerDisj = mkDisj midEx rightEx;
    val goalC = sumsqBody (pow pT vT);

    (* ---- case p = 2 : pow2_sumsq at e=v, rewrite 2 -> p ---- *)
    val caseTwo =
      let
        val h2 = Thm.assume (ctermGR (jT Aterm));   (* oeq p 2 *)
        (* pow2_sumsq_sch : sumsq (pow 2 e), schematic e_p2v.  At e=v : sumsq (pow 2 v). *)
        val pw2v = beta_norm (Drule.infer_instantiate ctxtGR [(("e_p2v",0), ctermGR vT)] pow2_sumsq_sch);
        (* rewrite (pow 2 v) -> (pow p v) via oeq 2 p (sym of h2) inside sumsq *)
        val h2sym = oeqSym_gr h2;                    (* oeq 2 p *)
        val zRW = Free("z_ct2", natT);
        val Prw = Term.lambda zRW (sumsqBody (pow zRW vT));
        val res = oeq_subst_gr_at (Prw, n2, pT) h2sym pw2v;   (* sumsq (pow p v) *)
      in Thm.implies_intr (ctermGR (jT Aterm)) res end;

    (* ---- case p = 4k+1 : convert mult-4 form -> fourk form, apply p1mod4_pow_sumsq ---- *)
    val caseMid =
      let
        val hM = Thm.assume (ctermGR (jT midEx));    (* Ex k. p = mult4 k + 1 *)
        (* rebuild to perprime's p1mod4Body form: Ex k. p = fourk k + 1 *)
        val kP1 = Term.lambda (Free("k_m", natT)) (oeq pT (add (mult n4 (Free("k_m", natT))) n1));
        val res = exE_r (kP1, goalC) hM "kmid_ct" natT (fn kF => fn hpk =>
          let
            (* hpk : oeq p (add (mult 4 k) 1).  rewrite mult4 k -> fourk k via mult4_to_fk. *)
            val br = mult4_to_fk kF;                  (* oeq (mult 4 k) ((k+k)+(k+k)) *)
            val cong = add_cong_l_gr (mult n4 kF, add (add kF kF)(add kF kF), n1) br;
                       (* oeq (add (mult4 k) 1)(add (fourk k) 1) *)
            val hpkF = oeqTrans_gr (hpk, cong);       (* oeq p (add (fourk k) 1) *)
            (* build p1mod4Body p : Ex k. p = add (fourk k) (Suc 0), witness k *)
            val p1Pred = Term.lambda (Free("k_b1",natT)) (oeq pT (add (add (add (Free("k_b1",natT)) (Free("k_b1",natT)))(add (Free("k_b1",natT)) (Free("k_b1",natT)))) n1));
            val exP1 = exI_r p1Pred kF hpkF;          (* jT (p1mod4Body p) *)
            (* p1mod4_pow_sumsq : (Ex k. p=4k+1) ==> prime2 p ==> sumsq (pow p e), schematic p_b1,e_b1 *)
            val ppsAt = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("p_b1",0), ctermGR pT),(("e_b1",0), ctermGR vT)] p1mod4_pow_sumsq_sch);
            val r1 = Thm.implies_elim ppsAt exP1;     (* prime2 p ==> sumsq (pow p v) *)
            val r2 = Thm.implies_elim r1 hPp;         (* sumsq (pow p v) *)
          in r2 end);
      in Thm.implies_intr (ctermGR (jT midEx)) res end;

    (* ---- case p = 4k+3 : need v even (from H at p,v + hVpv), apply p3mod4_even_sumsq ---- *)
    val caseRight =
      let
        val hR = Thm.assume (ctermGR (jT rightEx));   (* Ex k. p = mult4 k + 3 *)
        (* (1) build fourk3 p from rightEx (convert mult4 -> (((k+k)+k)+k)) *)
        val kP3 = Term.lambda (Free("k_r", natT)) (oeq pT (add (mult n4 (Free("k_r", natT))) n3));
        val res = exE_r (kP3, goalC) hR "kr_ct" natT (fn kF => fn hpk =>
          let
            (* hpk : oeq p (add (mult 4 k) 3) *)
            (* (1a) fourk3 form : oeq p (add (((k+k)+k)+k) 3) via mult4_to_fk3 *)
            val br3 = mult4_to_fk3 kF;                 (* oeq (mult 4 k) (((k+k)+k)+k) *)
            val cong3 = add_cong_l_gr (mult n4 kF, add (add (add kF kF) kF) kF, n3) br3;
            val hpkF3 = oeqTrans_gr (hpk, cong3);      (* oeq p (add (((k+k)+k)+k) 3) *)
            (* build fourk3 p : Ex k. p = add ((((k+k)+k)+k)) (Suc(Suc(Suc 0))) *)
            val f3body = fourk3Body pT;                (* Abs k. oeq p (add ((((k+k)+k)+k)) 3) *)
            val exF3 = exI_r f3body kF hpkF3;          (* jT (fourk3 p) *)
            (* (1b) perprime p3mod4Body form : Ex k. p = add (fourk k) 3 (fourk = (k+k)+(k+k)) *)
            val brf = mult4_to_fk kF;                  (* oeq (mult 4 k) ((k+k)+(k+k)) *)
            val congf = add_cong_l_gr (mult n4 kF, add (add kF kF)(add kF kF), n3) brf;
            val hpkFf = oeqTrans_gr (hpk, congf);      (* oeq p (add (fourk k) 3) *)
            val p3Pred = Term.lambda (Free("k_c3",natT)) (oeq pT (add (add (add (Free("k_c3",natT)) (Free("k_c3",natT)))(add (Free("k_c3",natT)) (Free("k_c3",natT)))) n3));
            val exP3 = exI_r p3Pred kF hpkFf;          (* jT (p3mod4Body p) *)
            (* (2) v even : H_pred n at p, then at v, mp with vpred p n v *)
            val hHatP = allE_r (Term.lambda pFrH (hpInnerBody nT pFrH)) pT hH;   (* hpInnerBody n p *)
            val st1 = mp_r (prime2 pT, mkImp (fourk3 pT) (innerAllE nT pT)) hHatP hPp;
            val st2 = mp_r (fourk3 pT, innerAllE nT pT) st1 exF3;   (* Forall(%e. Imp(vpred p n e)(even e)) *)
            val hAtV = allE_r (Term.lambda eFrH (mkImp (vpredBody (pT, nT, eFrH)) (evenBody eFrH))) vT st2;
                       (* Imp (vpred p n v)(even v) *)
            val hEvenV = mp_r (vpredBody (pT, nT, vT), evenBody vT) hAtV hVpv;   (* even v = Ex j. v=j+j *)
            (* (3) p3mod4_even_sumsq : (Ex k. p=4k+3) ==> (Ex j. e=2j) ==> sumsq (pow p e) *)
            val pesAt = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("p_c3",0), ctermGR pT),(("e_c3",0), ctermGR vT)] (varify p3mod4_even_sumsq));
            val r1 = Thm.implies_elim pesAt exP3;      (* (Ex j. v=2j) ==> sumsq (pow p v) *)
            val r2 = Thm.implies_elim r1 hEvenV;       (* sumsq (pow p v) *)
          in r2 end);
      in Thm.implies_intr (ctermGR (jT rightEx)) res end;

    (* combine : disjE on the inner disj, then outer *)
    val innerRes = disjE_r (midEx, rightEx, goalC) (Thm.assume (ctermGR (jT innerDisj))) caseMid caseRight;
    val innerArm = Thm.implies_intr (ctermGR (jT innerDisj)) innerRes;
    val full = disjE_r (Aterm, innerDisj, goalC) triDisj caseTwo innerArm;
  in full end;

val () = out "TSF_IFDIR_CLASSIFY_OK\n";
(* ============================================================================
   THE IF-DIRECTION : the strong induction proper.
     if_direction : 0 < n ==> hpBody n ==> sumsq n     (schematic n)
   ============================================================================ *)
val () = out "TSF_IFDIR_STRONG_BEGIN\n";

val if_direction =
  let
    val nStep = Free("n_if", natT);
    (* P n = Imp (lt 0 n)(Imp (hpBody n)(sumsqBody n))  -- object implications *)
    fun predBody nT = mkImp (lt ZeroC nT) (mkImp (hpBody nT) (sumsqBody nT));
    val GpropMeta = Logic.all (Free("m_ig",natT))
          (Logic.mk_implies (jT (lt (Free("m_ig",natT)) nStep), jT (predBody (Free("m_ig",natT)))));
    val IHbox = Thm.assume (ctermGR GpropMeta);
    fun applyIH mT (ltThm:thm) = Thm.implies_elim (Thm.forall_elim (ctermGR mT) IHbox) ltThm;  (* predBody m *)
    val hPosP = jT (lt ZeroC nStep); val hPos = Thm.assume (ctermGR hPosP);
    val hHP   = jT (hpBody nStep);   val hH   = Thm.assume (ctermGR hHP);
    val goalC = sumsqBody nStep;

    (* EM on (lt 1 n) : n>=2 vs n=1 *)
    val emN = em_gr (lt n1if nStep);

    (* ---- case ~lt 1 n : n=1 (with 0<n) -> sumsq 1 = sumsq n ---- *)
    val caseN1 =
      let
        val hNlt = Thm.assume (ctermGR (jT (neg (lt n1if nStep))));
        val leN1 = nlt_le_g (n1if, nStep) hNlt;            (* le n 1 *)
        (* le 1 n = lt 0 n = hPos *)
        val le1N = hPos;                                    (* le 1 n (since lt 0 n = le (Suc 0) n) *)
        val nEq1 = le_antisym_g (nStep, n1if) leN1 le1N;    (* oeq n 1 *)
        (* sumsq 1 -> sumsq n : oeq 1 n (sym) into %z. sumsq z *)
        val nEq1sym = oeqSym_gr nEq1;                        (* oeq 1 n *)
        val zRW = Free("z_n1", natT); val Prw = Term.lambda zRW (sumsqBody zRW);
        val res = oeq_subst_gr_at (Prw, n1if, nStep) nEq1sym sumsq_one_if;  (* sumsq n *)
      in Thm.implies_intr (ctermGR (jT (neg (lt n1if nStep)))) res end;

    (* ---- case lt 1 n : the main argument ---- *)
    val caseN2 =
      let
        val hLt1 = Thm.assume (ctermGR (jT (lt n1if nStep)));   (* lt 1 n = le 2 n *)
        (* prime_divisor_exists at n : le 2 n ==> Ex p. prime2 p /\ p|n *)
        val pdeAt = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR nStep)] (varify prime_divisor_exists));
        (* le 2 n is definitionally lt 1 n ; hLt1 has that exact term *)
        val pdEx = Thm.implies_elim pdeAt hLt1;             (* Ex p. prime2 p /\ p|n *)
        val pPred = Term.lambda (Free("p_rb", natT)) (mkConj (prime2 (Free("p_rb", natT))) (dvd (Free("p_rb", natT)) nStep));
        val res = exE_r (pPred, goalC) pdEx "p_if" natT (fn pF => fn hConjP =>
          let
            val hPp   = conjunct1_gr_at (prime2 pF, dvd pF nStep) hConjP;   (* prime2 p *)
            val hDpn  = conjunct2_gr_at (prime2 pF, dvd pF nStep) hConjP;   (* p|n *)
            val hLe2P = prime2_gt1_r pF hPp;                                (* le 2 p = lt 1 p *)
            (* padic_split at p,n : prime2 p ==> lt 0 n ==> vpredEBody p n *)
            val psAt = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("p",0), ctermGR pF),(("n_ps",0), ctermGR nStep)] padic_split);
            val ps1 = mp_r (prime2 pF, mkImp (lt ZeroC nStep) (vpredEBody pF nStep)) psAt hPp;
            val ps2 = mp_r (lt ZeroC nStep, vpredEBody pF nStep) ps1 hPos;  (* vpredEBody p n *)
            (* exE over e (=v) *)
            val ePred = Term.lambda eFrV (vpredBody (pF, nStep, eFrV));
            val res2 = exE_r (ePred, goalC) ps2 "v_if" natT (fn vF => fn hVe =>
              let
                (* hVe : vpredBody (p,n,v) = Ex m. n=p^v*m /\ ~p|m *)
                val mPred = Term.lambda mFrV (mkConj (oeq nStep (mult (pow pF vF) mFrV)) (neg (dvd pF mFrV)));
                val res3 = exE_r (mPred, goalC) hVe "m_if" natT (fn mF => fn hConjM =>
                  let
                    val hNeq  = conjunct1_gr_at (oeq nStep (mult (pow pF vF) mF), neg (dvd pF mF)) hConjM;  (* n = p^v*m *)
                    val hNdm  = conjunct2_gr_at (oeq nStep (mult (pow pF vF) mF), neg (dvd pF mF)) hConjM;  (* ~p|m *)
                    (* rebuild vpredBody p n v (= hVpv) for classify : we have it as hVe? no, hVe is the
                       full Ex-m body.  Rebuild from witness m + hConjM. *)
                    val hVpv = exI_r (Term.lambda mFrV (mkConj (oeq nStep (mult (pow pF vF) mFrV)) (neg (dvd pF mFrV)))) mF hConjM;
                               (* vpredBody (p,n,v) *)
                    (* ---- 0 < m ---- *)
                    val hPosM =
                      let val dzM = dzos_gr mF                (* Disj (m=0)(Ex q. m=Suc q) *)
                          val caseZ =
                            let val hz = Thm.assume (ctermGR (jT (oeq mF ZeroC)))
                                (* n = p^v*m, m=0 -> n = p^v*0 = 0 -> contra 0<n *)
                                val cz = mult_cong_r_g (pow pF vF, mF, ZeroC) hz   (* p^v*m = p^v*0 *)
                                val p0 = mult0r_g (pow pF vF)                       (* p^v*0 = 0 *)
                                val nEq0 = oeqTrans_r2 (hNeq, oeqTrans_r2 (cz, p0)) (* n = 0 *)
                                val z = Free("z0m_if", natT); val Plt = Term.lambda z (lt ZeroC z)
                                val lt00 = oeq_rw_r (Plt, nStep, ZeroC) nEq0 hPos  (* lt 0 0 *)
                                val fls = lt_irrefl_g ZeroC lt00
                            in Thm.implies_intr (ctermGR (jT (oeq mF ZeroC))) (Thm.implies_elim (oFalse_elim_r (lt ZeroC mF)) fls) end
                          val caseS =
                            let val hsP = jT (mkExSuc mF); val hs = Thm.assume (ctermGR hsP)
                                val b = exE_r (Abs("q",natT,oeq mF (suc (Bound 0))), lt ZeroC mF) hs "qm_if" natT (fn qF => fn hq =>
                                          let val l0sq = lt_zero_suc_g qF
                                              val z = Free("zsm_if", natT); val Plt = Term.lambda z (lt ZeroC z)
                                          in oeq_rw_r (Plt, suc qF, mF) (oeqSym_r2 hq) l0sq end)
                            in Thm.implies_intr (ctermGR hsP) b end
                      in disjE_r (oeq mF ZeroC, mkExSuc mF, lt ZeroC mF) dzM caseZ caseS end;
                    (* ---- v = Suc w (v>=1) ---- *)
                    val hVsuc =       (* jT (Ex w. v = Suc w) *)
                      let val dzV = dzos_gr vF
                          val caseZ =
                            let val hz = Thm.assume (ctermGR (jT (oeq vF ZeroC)))
                                (* v=0 -> p^v=p^0=1 -> n=1*m=m -> p|n=p|m contra ~p|m *)
                                val pvCong = let val Pp = Term.lambda (Free("zv0",natT)) (oeq (pow pF vF)(pow pF (Free("zv0",natT))))
                                             in oeq_rw_r (Pp, vF, ZeroC) hz (oeqRefl_r2 (pow pF vF)) end   (* pow p v = pow p 0 *)
                                val pz = powZero_gr pF                              (* pow p 0 = 1 *)
                                val pv1 = oeqTrans_r2 (pvCong, pz)                  (* pow p v = 1 *)
                                (* n = p^v*m = 1*m = m *)
                                val c1 = mult_cong_l_gr (pow pF vF, n1if, mF) pv1   (* p^v*m = 1*m *)
                                val m1 = mult1l_gr mF                               (* 1*m = m *)
                                val nEqM = oeqTrans_r2 (hNeq, oeqTrans_r2 (c1, m1)) (* n = m *)
                                (* p|n -> p|m (rewrite dvd p n -> dvd p m via oeq n m) *)
                                val z = Free("zdvm_if", natT); val Pd = Term.lambda z (dvd pF z)
                                val hDpm = oeq_rw_r (Pd, nStep, mF) nEqM hDpn       (* p|m *)
                                val fls = mp_r (dvd pF mF, oFalseC) hNdm hDpm       (* oFalse *)
                            in Thm.implies_intr (ctermGR (jT (oeq vF ZeroC))) (Thm.implies_elim (oFalse_elim_r (mkExSuc vF)) fls) end
                          val caseS =
                            let val hsP = jT (mkExSuc vF); val hs = Thm.assume (ctermGR hsP)
                            in Thm.implies_intr (ctermGR hsP) hs end
                      in disjE_r (oeq vF ZeroC, mkExSuc vF, mkExSuc vF) dzV caseZ caseS end;
                    (* ---- m < n : from v=Suc w, le 2 (p^v), lt m (p^v*m), rewrite p^v*m=n ---- *)
                    val hLtMN = exE_r (Abs("w",natT,oeq vF (suc (Bound 0))), lt mF nStep) hVsuc "w_if" natT (fn wF => fn hvw =>
                      let
                        (* le 2 (p^v) : rewrite v -> Suc w then pow_ge_2 *)
                        val le2pSw = pow_ge_2 (pF, wF) hLe2P                  (* le 2 (pow p (Suc w)) *)
                        val z1 = Free("zpv_if", natT); val Plv = Term.lambda z1 (le n2if (pow pF z1))
                        val le2pv = oeq_rw_r (Plv, suc wF, vF) (oeqSym_r2 hvw) le2pSw  (* le 2 (pow p v) *)
                        (* lt m (p^v * m) *)
                        val ltmpvm = lt_m_Km (mF, pow pF vF) hPosM le2pv     (* lt m (pow p v * m) *)
                        (* rewrite (pow p v * m) -> n via oeq n (p^v*m) sym *)
                        val z2 = Free("zmn_if", natT); val Plt2 = Term.lambda z2 (lt mF z2)
                      in oeq_rw_r (Plt2, mult (pow pF vF) mF, nStep) (oeqSym_r2 hNeq) ltmpvm end);
                    (* ---- IH at m -> sumsq m ---- *)
                    val predM = applyIH mF hLtMN;                            (* predBody m *)
                    val pm1 = mp_r (lt ZeroC mF, mkImp (hpBody mF) (sumsqBody mF)) predM hPosM;  (* hpBody m ==> sumsq m *)
                    (* hpBody m via val_transfer (a META-implication chain :
                       prime2 q ==> ~q|m ==> n=q^v*m ==> hpBody n ==> hpBody m) ;
                       apply with OF / implies_elim, NOT mp_r. *)
                    val vtAt = beta_norm (Drule.infer_instantiate ctxtGR
                                 [(("q",0), ctermGR pF),(("m",0), ctermGR mF),(("v",0), ctermGR vF),(("n",0), ctermGR nStep)] val_transfer);
                    val hHm = ((((vtAt OF [hPp]) OF [hNdm]) OF [hNeq]) OF [hH]);   (* hpBody m *)
                    val sqM = mp_r (hpBody mF, sumsqBody mF) pm1 hHm;         (* sumsq m *)
                    (* ---- sumsq (p^v) via classify ---- *)
                    val sqPv = classify_pow_sumsq (pF, vF, nStep) hPp hH hVpv;  (* sumsq (pow p v) *)
                    (* ---- sumsq (p^v * m) = sumsq n ---- *)
                    val sqProd = sumsq_mult (pow pF vF, mF) sqPv sqM;        (* sumsq (pow p v * m) *)
                    val z = Free("zfin_if", natT); val Prw = Term.lambda z (sumsqBody z);
                    val sqN = oeq_subst_gr_at (Prw, mult (pow pF vF) mF, nStep) (oeqSym_r2 hNeq) sqProd;  (* sumsq n *)
                  in sqN end);
              in res3 end);
          in res2 end);
      in Thm.implies_intr (ctermGR (jT (lt n1if nStep))) res end;

    val bodyN = disjE_r (lt n1if nStep, neg (lt n1if nStep), goalC) emN caseN2 caseN1;  (* sumsq n , under hPos,hH *)
    (* object-ify : predBody n = Imp (lt 0 n)(Imp (hpBody n)(sumsq n)) *)
    val predN = impI_r (lt ZeroC nStep, mkImp (hpBody nStep)(sumsqBody nStep))
                  (Thm.implies_intr (ctermGR hPosP)
                    (impI_r (hpBody nStep, sumsqBody nStep)
                       (Thm.implies_intr (ctermGR hHP) bodyN)));
    val stepAll = Thm.forall_intr (ctermGR nStep) (Thm.implies_intr (ctermGR GpropMeta) predN);
    val predAbs = Term.lambda nStep (predBody nStep);
    val si_inst = beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR predAbs),(("k",0), ctermGR nStep)] (varify strong_induct));
    val predNStep = Thm.implies_elim si_inst stepAll;   (* predBody n , 0-hyp *)
  in varify predNStep end;

val () = out ("TSF_IFDIR_STRONG_BUILT hyps="^Int.toString(length(Thm.hyps_of if_direction))^"\n");

(* ---- validation : 0-hyp + aconv intended ---- *)
val if_direction_intended =
  let val nV = Var(("n_if",0), natT)
  in jT (mkImp (lt ZeroC nV) (mkImp (hpBody nV) (sumsqBody nV))) end;
val ifd_hyps = length (Thm.hyps_of if_direction);
val ifd_aconv = (Thm.prop_of if_direction) aconv if_direction_intended;
val () = out ("IF_DIRECTION hyps="^Int.toString ifd_hyps^" aconv="^Bool.toString ifd_aconv^"\n");

(* soundness probe 1 : must KEEP 0<n (drop it -> not aconv ; false for n=0 with vacuous H) *)
val ifd_probe1 =
  let val nV = Var(("n_if",0), natT)
      val bogus = jT (mkImp (hpBody nV) (sumsqBody nV))
  in not ((Thm.prop_of if_direction) aconv bogus) end;
(* soundness probe 2 : must KEEP the H hypothesis (drop it -> not aconv ; false for n=3) *)
val ifd_probe2 =
  let val nV = Var(("n_if",0), natT)
      val bogus = jT (mkImp (lt ZeroC nV) (sumsqBody nV))
  in not ((Thm.prop_of if_direction) aconv bogus) end;
val () = if ifd_probe1 then out "PROBE_OK if_direction keeps 0<n\n" else out "PROBE_FAIL if_direction dropped 0<n\n";
val () = if ifd_probe2 then out "PROBE_OK if_direction keeps the even-valuation hypothesis H\n" else out "PROBE_FAIL if_direction dropped H\n";
val () = if ifd_hyps = 0 andalso ifd_aconv andalso ifd_probe1 andalso ifd_probe2
         then out "IF_DIRECTION_CLOSED\n" else out ("IF_DIRECTION_FAILED hyps="^Int.toString ifd_hyps^" aconv="^Bool.toString ifd_aconv^"\n");
val () = out "TSF_IFDIR_STRONG_DONE\n";
