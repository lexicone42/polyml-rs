
(* ############################################################################
   ####  EISENSTEIN BRIDGE  (fleet F2)  ########################################
   APPENDED to qr_f1_toolbox.sml (ends at TOOLBOX_ALL_OK on ctxtT/ctermT/thyT).
   ALL on the ONE final context ctxtT (= ctxtGG + parity + cnt).  No new const.
   Stages:
     (SP) split + lar decomposition per k : q*k = p*(rdiv) + rmod, rmod<p ;
          lar relation ; flip predicate.        marker EIS_SPLIT_OK
     (PB) parity bridge : mu == sumf (\k. rdiv (q*k) p) (Suc m) (mod 2)
          where mu = cnt (flip-predicate) m.     marker EIS_PARITY_OK
     (EL) eisenstein lemma : the gauss sign for q mod p is determined by
          parity of (sumf floor) (Suc m).        marker EIS_LEMMA_OK
   ############################################################################ *)
val () = out "EISENSTEIN_BRIDGE_BEGIN\n";

(* ----------------------------------------------------------------------------
   Additional re-varified base lemmas onto ctxtT needed for the bridge.
   ---------------------------------------------------------------------------- *)
val mult_0_T_b      = varifyT mult_0_v;        (* oeq (mult 0 n) 0 *)
val mult_Suc_T_b    = varifyT mult_Suc_v;      (* oeq (mult (Suc m) n)(add n (mult m n)) *)
fun mult0l_T t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] mult_0_T_b);
fun multSuc_T_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtT
      [(("m",0), ctermT mt),(("n",0), ctermT nt)] mult_Suc_T_b);

(* add_0 (left) : oeq (add 0 n) n  on ctxtT *)
val add_0_left_T   = varifyT add_0;
fun add_0_left_T_at t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] add_0_left_T);

(* CAUTION: the earlier T-stage (line ~870-904) defines addassocT_at / addcommT_at /
   etc. CLOSED OVER AN OLDER ctxtT (a theory WITHOUT rdiv).  The Eisenstein toolbox
   REBINDS ctxtT to thyT (with rdiv) at the TOOLBOX_CTX_READY block.  So we must NOT
   reuse those stale instantiators on rdiv-carrying terms — rebuild fresh ones bound
   to the CURRENT ctxtT. *)
val add_assoc_T2   = varifyT add_assoc;
fun addassoc_T2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtT
      [(("m",0), ctermT mt),(("n",0), ctermT nt),(("k",0), ctermT kt)] add_assoc_T2);

(* parity 1 = 1 is parity1_eq (already proved).  expose value witnesses *)
(* mult_1_left_T : oeq (mult 1 n) n  (already varified at toolbox) *)
fun mult1l_T_b t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] mult_1_left_T);

(* ============================================================================
   (M)  PARITY OF PRODUCTS :  parity_mult_l  +  parity_odd_mult
   parity_mult_l : parity(mult a b) = parity(mult (parity a) b)   BY INDUCTION on a
   (mirror parity_norm_l, but with mult / mult_Suc; reuses parity_add, parity_idem,
    parity_bounded, sub1_invol_bounded_at)
   ============================================================================ *)
val () = out "M_PARITYMULT_BEGIN\n";

(* mult_cong_l on ctxtT : from (hpq : oeq p q) build oeq (mult p k)(mult q k) *)
fun mult_cong_l_T (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_T (Pabs, pT, qT) hpq (oeqRefl_T (mult pT kT)) end;

val parity_mult_l =
  let
    val bF = Free("b", natT);
    val kF = Free("a", natT);
    val Pabs = Abs("z", natT, oeq (parity (mult (Bound 0) bF)) (parity (mult (parity (Bound 0)) bF)));
    (* BASE a=0 : parity(mult 0 b) = parity(mult (parity 0) b) *)
    val baseThm =
      let
        (* RHS : parity(mult (parity 0) b) ; rewrite parity 0 -> 0 : parity(mult 0 b) *)
        val inAbs = Abs("z", natT, oeq (parity (mult (parity ZeroC) bF)) (parity (mult (Bound 0) bF)));
        val cg = oeq_rw_T (inAbs, parity ZeroC, ZeroC) parity_0_T (oeqRefl_T (parity (mult (parity ZeroC) bF)));
                 (* parity(mult (parity 0) b) = parity(mult 0 b) *)
      in oeq_sym_T OF [cg] end;   (* parity(mult 0 b) = parity(mult (parity 0) b) *)
    (* STEP a -> Suc a *)
    val xF = Free("x", natT);
    val ihP = jT (oeq (parity (mult xF bF)) (parity (mult (parity xF) bF)));
    val IH  = Thm.assume (ctermT ihP);
    val stepConcl =
      let
        (* LHS : parity(mult(Suc x)b) ; mult(Suc x)b = add b (mult x b)  [mult_Suc] *)
        val mS = multSuc_T_at (xF, bF);                (* mult(Suc x)b = add b (mult x b) *)
        val pcong = let val pAbs = Abs("z", natT, oeq (parity (mult (suc xF) bF)) (parity (Bound 0)))
                    in oeq_rw_T (pAbs, mult (suc xF) bF, add bF (mult xF bF)) mS
                               (oeqRefl_T (parity (mult (suc xF) bF))) end;
                    (* parity(mult(Suc x)b) = parity(add b (mult x b)) *)
        (* parity(add b (mult x b)) = parity(add (parity b)(parity(mult x b)))  [parity_add] *)
        val pa = beta_norm (Drule.infer_instantiate ctxtT
                   [(("a",0), ctermT bF),(("b",0), ctermT (mult xF bF))] parity_add);
        (* rewrite parity(mult x b) -> parity(mult (parity x) b) via IH inside add (parity b) (.) *)
        val raAbs = Abs("z", natT, oeq (parity (add (parity bF)(parity (mult xF bF))))
                                        (parity (add (parity bF)(Bound 0))));
        val paIH = oeq_rw_T (raAbs, parity (mult xF bF), parity (mult (parity xF) bF)) IH
                            (oeqRefl_T (parity (add (parity bF)(parity (mult xF bF)))));
                   (* parity(add(parity b)(parity(mult x b))) = parity(add(parity b)(parity(mult(parity x)b))) *)
        val lhsEq = oeq_trans_T OF [oeq_trans_T OF [pcong, pa], paIH];
                    (* parity(mult(Suc x)b) = parity(add(parity b)(parity(mult(parity x)b))) *)
        (* RHS : parity(mult (parity(Suc x)) b) ; parity(Suc x) = sub 1 (parity x) *)
        val pSx = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT xF)] parity_Suc_T);
                  (* parity(Suc x) = sub 1 (parity x) *)
        val rhsCg = let val rAbs = Abs("z", natT, oeq (parity (mult (parity (suc xF)) bF))
                                                       (parity (mult (Bound 0) bF)))
                    in oeq_rw_T (rAbs, parity (suc xF), sub oneC (parity xF)) pSx
                               (oeqRefl_T (parity (mult (parity (suc xF)) bF))) end;
                    (* parity(mult(parity(Suc x))b) = parity(mult(sub 1(parity x))b) *)
        (* MID : parity(add(parity b)(parity(mult(parity x)b))) = parity(mult(sub 1(parity x))b)
           case on parity x via parity_bounded *)
        val pbx = parity_bounded_at xF;
        val midGoal = oeq (parity (add (parity bF)(parity (mult (parity xF) bF))))
                          (parity (mult (sub oneC (parity xF)) bF));
        val cA =   (* parity x = 0 *)
          let
            val hz = Thm.assume (ctermT (jT (oeq (parity xF) ZeroC)))
            (* LHS : rewrite parity x -> 0
               parity(add(parity b)(parity(mult 0 b)))  ; mult 0 b = 0 ; parity 0 = 0
               = parity(add(parity b) 0) = parity(parity b) [add0r] = parity b [idem] *)
            val l1Abs = Abs("z", natT, oeq (parity (add (parity bF)(parity (mult (parity xF) bF))))
                                           (parity (add (parity bF)(parity (mult (Bound 0) bF)))));
            val l1 = oeq_rw_T (l1Abs, parity xF, ZeroC) hz
                        (oeqRefl_T (parity (add (parity bF)(parity (mult (parity xF) bF)))));
                     (* = parity(add(parity b)(parity(mult 0 b))) *)
            val m0 = mult0l_T bF;                    (* mult 0 b = 0 *)
            val l2Abs = Abs("z", natT, oeq (parity (add (parity bF)(parity (mult ZeroC bF))))
                                           (parity (add (parity bF)(parity (Bound 0)))));
            val l2 = oeq_rw_T (l2Abs, mult ZeroC bF, ZeroC) m0
                        (oeqRefl_T (parity (add (parity bF)(parity (mult ZeroC bF)))));
                     (* = parity(add(parity b)(parity 0)) *)
            val l3Abs = Abs("z", natT, oeq (parity (add (parity bF)(parity ZeroC)))
                                           (parity (add (parity bF)(Bound 0))));
            val l3 = oeq_rw_T (l3Abs, parity ZeroC, ZeroC) parity_0_T
                        (oeqRefl_T (parity (add (parity bF)(parity ZeroC))));
                     (* = parity(add(parity b) 0) *)
            val a0r = add0r_T (parity bF);           (* add(parity b)0 = parity b *)
            val l4Abs = Abs("z", natT, oeq (parity (add (parity bF) ZeroC)) (parity (Bound 0)));
            val l4 = oeq_rw_T (l4Abs, add (parity bF) ZeroC, parity bF) a0r
                        (oeqRefl_T (parity (add (parity bF) ZeroC)));
                     (* parity(add(parity b)0) = parity(parity b) *)
            val l5i = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT bF)] parity_idem);
                      (* parity(parity b) = parity b *)
            val lhsChain2 = oeq_trans_T OF [l4, l5i];   (* parity(add(parity b)0) = parity b *)
            val lhsFull = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [l1,l2], l3], lhsChain2];
                          (* parity(add(parity b)(parity(mult(parity x)b))) = parity b *)
            (* RHS : parity(mult(sub 1(parity x))b) ; parity x->0 ; sub 1 0 = 1 ; mult 1 b = b *)
            val r1Abs = Abs("z", natT, oeq (parity (mult (sub oneC (parity xF)) bF))
                                           (parity (mult (sub oneC (Bound 0)) bF)));
            val r1 = oeq_rw_T (r1Abs, parity xF, ZeroC) hz
                        (oeqRefl_T (parity (mult (sub oneC (parity xF)) bF)));
                     (* = parity(mult(sub 1 0)b) *)
            val r2Abs = Abs("z", natT, oeq (parity (mult (sub oneC ZeroC) bF))
                                           (parity (mult (Bound 0) bF)));
            val r2 = oeq_rw_T (r2Abs, sub oneC ZeroC, oneC) sub1_0
                        (oeqRefl_T (parity (mult (sub oneC ZeroC) bF)));
                     (* = parity(mult 1 b) *)
            val m1 = mult1l_T_b bF;                   (* mult 1 b = b *)
            val r3Abs = Abs("z", natT, oeq (parity (mult oneC bF)) (parity (Bound 0)));
            val r3 = oeq_rw_T (r3Abs, mult oneC bF, bF) m1
                        (oeqRefl_T (parity (mult oneC bF)));
                     (* parity(mult 1 b) = parity b *)
            val rhsChain = oeq_trans_T OF [oeq_trans_T OF [r1, r2], r3];
                           (* parity(mult(sub 1(parity x))b) = parity b *)
            val res = oeq_trans_T OF [lhsFull, oeq_sym_T OF [rhsChain]];
          in Thm.implies_intr (ctermT (jT (oeq (parity xF) ZeroC))) res end;
        val cB =   (* parity x = 1 *)
          let
            val ho = Thm.assume (ctermT (jT (oeq (parity xF) oneC)))
            (* LHS : parity x -> 1
               parity(add(parity b)(parity(mult 1 b)))  ; mult 1 b = b ; parity(parity b) wraps?
               actually parity(mult (parity x) b) with parity x=1 -> parity(mult 1 b)=parity b
               so LHS = parity(add(parity b)(parity b)) *)
            val l1Abs = Abs("z", natT, oeq (parity (add (parity bF)(parity (mult (parity xF) bF))))
                                           (parity (add (parity bF)(parity (mult (Bound 0) bF)))));
            val l1 = oeq_rw_T (l1Abs, parity xF, oneC) ho
                        (oeqRefl_T (parity (add (parity bF)(parity (mult (parity xF) bF)))));
                     (* = parity(add(parity b)(parity(mult 1 b))) *)
            val m1 = mult1l_T_b bF;                   (* mult 1 b = b *)
            val l2Abs = Abs("z", natT, oeq (parity (add (parity bF)(parity (mult oneC bF))))
                                           (parity (add (parity bF)(parity (Bound 0)))));
            val l2 = oeq_rw_T (l2Abs, mult oneC bF, bF) m1
                        (oeqRefl_T (parity (add (parity bF)(parity (mult oneC bF)))));
                     (* = parity(add(parity b)(parity b)) *)
            (* parity(add(parity b)(parity b)) : parity_add -> parity(add(parity(parity b))(parity(parity b)))
               idem on each : = parity(add(parity b)(parity b)).  Need this = 0 ... NO.
               Better: x+x is even.  parity(add z z) = 0 for any z.  Prove via parity_add:
               parity(add z z) = parity(add(parity z)(parity z)).  case parity z =0/1:
                 0 : parity(add 0 0)=parity 0=0
                 1 : parity(add 1 1)=parity(Suc(Suc 0))=sub 1(parity(Suc 0))=sub 1 1=0
               So parity(add z z) = 0 . Use z = parity b. *)
            val pdbl =   (* parity(add (parity b)(parity b)) = 0 *)
              let
                val zT = parity bF;
                val pa = beta_norm (Drule.infer_instantiate ctxtT
                           [(("a",0), ctermT zT),(("b",0), ctermT zT)] parity_add);
                          (* parity(add z z) = parity(add(parity z)(parity z)) *)
                val pbz = parity_bounded_at zT;  (* Disj(parity z=0)(parity z=1) *)
                val gg = oeq (parity (add zT zT)) ZeroC;
                val ca2 =
                  let
                    val hz2 = Thm.assume (ctermT (jT (oeq (parity zT) ZeroC)))
                    (* parity(add(parity z)(parity z)) with parity z->0 : parity(add 0 0) = parity 0 = 0 *)
                    val w1Abs = Abs("z", natT, oeq (parity (add (parity zT)(parity zT)))
                                                   (parity (add (Bound 0)(parity zT))));
                    val w1 = oeq_rw_T (w1Abs, parity zT, ZeroC) hz2
                                (oeqRefl_T (parity (add (parity zT)(parity zT))));
                             (* = parity(add 0 (parity z)) *)
                    val w2Abs = Abs("z", natT, oeq (parity (add ZeroC (parity zT)))
                                                   (parity (add ZeroC (Bound 0))));
                    val w2 = oeq_rw_T (w2Abs, parity zT, ZeroC) hz2
                                (oeqRefl_T (parity (add ZeroC (parity zT))));
                             (* = parity(add 0 0) *)
                    val a00 = add0r_T ZeroC;  (* add 0 0 = 0 *)
                    val w3Abs = Abs("z", natT, oeq (parity (add ZeroC ZeroC)) (parity (Bound 0)));
                    val w3 = oeq_rw_T (w3Abs, add ZeroC ZeroC, ZeroC) a00
                                (oeqRefl_T (parity (add ZeroC ZeroC)));
                             (* parity(add 0 0) = parity 0 *)
                    val tozero = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [pa, w1], w2],
                                                 oeq_trans_T OF [w3, parity_0_T]];
                  in Thm.implies_intr (ctermT (jT (oeq (parity zT) ZeroC))) tozero end;
                val cb2 =
                  let
                    val ho2 = Thm.assume (ctermT (jT (oeq (parity zT) oneC)))
                    (* parity(add 1 1) = parity(Suc(Suc 0)) ; add 1 1 = Suc(Suc 0)? add (Suc 0)(Suc 0).
                       parity_Suc twice : parity(Suc(add 0 (Suc 0))) = sub 1(parity(add 0 (Suc 0)))
                       use parityA_at(0, Suc 0): parity(add(Suc 0)(Suc 0)) = sub 1(parity(add 0 (Suc 0))) *)
                    val w1Abs = Abs("z", natT, oeq (parity (add (parity zT)(parity zT)))
                                                   (parity (add (Bound 0)(parity zT))));
                    val w1 = oeq_rw_T (w1Abs, parity zT, oneC) ho2
                                (oeqRefl_T (parity (add (parity zT)(parity zT))));
                             (* = parity(add 1 (parity z)) *)
                    val w2Abs = Abs("z", natT, oeq (parity (add oneC (parity zT)))
                                                   (parity (add oneC (Bound 0))));
                    val w2 = oeq_rw_T (w2Abs, parity zT, oneC) ho2
                                (oeqRefl_T (parity (add oneC (parity zT))));
                             (* = parity(add 1 1) = parity(add(Suc 0)(Suc 0)) *)
                    val la = parityA_at (ZeroC, oneC);  (* parity(add(Suc 0)(Suc 0)) = sub 1(parity(add 0 (Suc 0))) *)
                    (* parity(add 0 (Suc 0)) : add 0 (Suc 0) ... need add_0_left? we have add0r (right).
                       use parity(add 0 (Suc 0)): rewrite via add_0_left? Instead compute add 0 1 via
                       parityA again is for Suc on left.  Simpler: add 0 (Suc 0) -- use add_0_left fact.
                       We'll prove parity(add 0 (Suc 0)) = 1 via: add 0 n = n needs add_0_left.
                       Alternative: avoid by using z+z form with parityA on the OUTER:
                       Actually we have add 1 1 = add (Suc 0)(Suc 0).  la gives = sub 1(parity(add 0 (Suc 0))).
                       parity(add 0 (Suc 0)) = parity(Suc 0) IF add 0 (Suc 0)=Suc 0 (add_0_left). *)
                    val a0l = add_0_left_T_at (suc ZeroC);  (* add 0 (Suc 0) = Suc 0 *)
                    val w3Abs = Abs("z", natT, oeq (parity (add ZeroC (suc ZeroC))) (parity (Bound 0)));
                    val w3 = oeq_rw_T (w3Abs, add ZeroC (suc ZeroC), suc ZeroC) a0l
                                (oeqRefl_T (parity (add ZeroC (suc ZeroC))));
                             (* parity(add 0 (Suc 0)) = parity(Suc 0) *)
                    val p1 = parity1_eq;  (* parity(Suc 0) = 1 *)
                    val inner = oeq_trans_T OF [w3, p1];  (* parity(add 0 (Suc 0)) = 1 *)
                    (* sub 1(parity(add 0 (Suc 0))) = sub 1 1 = 0 *)
                    val laAbs = Abs("z", natT, oeq (sub oneC (parity (add ZeroC (suc ZeroC)))) (sub oneC (Bound 0)));
                    val la2 = oeq_rw_T (laAbs, parity (add ZeroC (suc ZeroC)), oneC) inner
                                (oeqRefl_T (sub oneC (parity (add ZeroC (suc ZeroC)))));
                             (* sub 1(parity(add 0 (Suc 0))) = sub 1 1 *)
                    val laFull = oeq_trans_T OF [la, oeq_trans_T OF [la2, sub1_1]];
                                 (* parity(add(Suc 0)(Suc 0)) = 0 *)
                    val tozero = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [pa, w1], w2], laFull];
                  in Thm.implies_intr (ctermT (jT (oeq (parity zT) oneC))) tozero end;
              in disjE_T_at (oeq (parity zT) ZeroC, oeq (parity zT) oneC, gg) pbz ca2 cb2 end;
            (* LHS = parity(add(parity b)(parity b)) = 0 *)
            val lhsFull = oeq_trans_T OF [oeq_trans_T OF [l1, l2], pdbl];  (* = 0 *)
            (* RHS : parity(mult(sub 1(parity x))b) ; parity x -> 1 ; sub 1 1 = 0 ; mult 0 b = 0 ; parity 0 = 0 *)
            val r1Abs = Abs("z", natT, oeq (parity (mult (sub oneC (parity xF)) bF))
                                           (parity (mult (sub oneC (Bound 0)) bF)));
            val r1 = oeq_rw_T (r1Abs, parity xF, oneC) ho
                        (oeqRefl_T (parity (mult (sub oneC (parity xF)) bF)));
                     (* = parity(mult(sub 1 1)b) *)
            val r2Abs = Abs("z", natT, oeq (parity (mult (sub oneC oneC) bF))
                                           (parity (mult (Bound 0) bF)));
            val r2 = oeq_rw_T (r2Abs, sub oneC oneC, ZeroC) sub1_1
                        (oeqRefl_T (parity (mult (sub oneC oneC) bF)));
                     (* = parity(mult 0 b) *)
            val m0 = mult0l_T bF;  (* mult 0 b = 0 *)
            val r3Abs = Abs("z", natT, oeq (parity (mult ZeroC bF)) (parity (Bound 0)));
            val r3 = oeq_rw_T (r3Abs, mult ZeroC bF, ZeroC) m0
                        (oeqRefl_T (parity (mult ZeroC bF)));
                     (* parity(mult 0 b) = parity 0 *)
            val rhsChain = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [r1, r2], r3], parity_0_T];
                           (* parity(mult(sub 1(parity x))b) = 0 *)
            val res = oeq_trans_T OF [lhsFull, oeq_sym_T OF [rhsChain]];
          in Thm.implies_intr (ctermT (jT (oeq (parity xF) oneC))) res end;
        val midEq = disjE_T_at (oeq (parity xF) ZeroC, oeq (parity xF) oneC, midGoal) pbx cA cB;
        val res = oeq_trans_T OF [oeq_trans_T OF [lhsEq, midEq], oeq_sym_T OF [rhsCg]];
      in res end;
    val stepF = Thm.forall_intr (ctermT xF) (Thm.implies_intr (ctermT ihP) stepConcl);
    val run = nat_induct_T_run Pabs kF baseThm stepF;
  in varify run end;
val aV_pm = Var(("a",0), natT); val bV_pm = Var(("b",0), natT);
val i_parity_mult_l = jT (oeq (parity (mult aV_pm bV_pm)) (parity (mult (parity aV_pm) bV_pm)));
val r_parity_mult_l = checkT ("parity_mult_l", parity_mult_l, i_parity_mult_l);

val () = if r_parity_mult_l then out "PARITY_MULT_L_OK\n" else out "PARITY_MULT_L_FAILED\n";
val () = out "M_PARITYMULT_END\n";

(* ============================================================================
   (SP) SPLIT + LAR DECOMPOSITION per k in [1,m]
   For 0<p :  mult a k = add (mult p (rdiv (mult a k) p)) (rmod (mult a k) p)
              AND  lt (rmod (mult a k) p) p.
   Plus the lar branch relations (lar_lo / lar_hi) lifted onto ctxtT, and the
   flip predicate flipP a p k := lt p (add (rOf a p k)(rOf a p k))  (= p < 2r).
   ============================================================================ *)
val () = out "SP_SPLIT_BEGIN\n";

(* lar_lo / lar_hi varified onto ctxtT *)
val lar_lo_T = varifyT lar_lo_ax;
val lar_hi_T = varifyT lar_hi_ax;
fun lar_lo_T_at (aT, pT, kT) hle =     (* 2r<=p -> lar = r *)
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtT
        [(("a",0), ctermT aT), (("p",0), ctermT pT), (("k",0), ctermT kT)] lar_lo_T)) hle;
fun lar_hi_T_at (aT, pT, kT) hlt =     (* p<2r -> lar = p-r *)
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtT
        [(("a",0), ctermT aT), (("p",0), ctermT pT), (("k",0), ctermT kT)] lar_hi_T)) hlt;

(* the flip predicate : p < 2*(rmod (a*k) p) *)
fun flipPred a p k = lt p (add (rOf a p k) (rOf a p k));
fun flipAbs a p = let val zk = Free("k_fl", natT) in Term.lambda zk (flipPred a p zk) end;

(* split_lemma : 0<p ==> Conj (split-eq) (rmod<p) *)
val split_lemma =
  let
    val aF = Free("a", natT); val pF = Free("p", natT); val kF = Free("k", natT);
    val hpos = Thm.assume (ctermT (jT (lt ZeroC pF)));
    val ak = mult aF kF;
    val divEq = div_mod_eq_T_at (ak, pF) hpos;   (* oeq ak (add (mult p (rdiv ak p))(rmod ak p)) *)
    val rlt   = rmod_lt_T_at (ak, pF) hpos;      (* lt (rmod ak p) p *)
    val conj  = conjI_T_at (oeq ak (add (mult pF (rdiv ak pF))(rmod ak pF)), lt (rmod ak pF) pF) divEq rlt;
    val d1 = Thm.implies_intr (ctermT (jT (lt ZeroC pF))) conj;
  in varify d1 end;
val aV_sp = Var(("a",0),natT); val pV_sp = Var(("p",0),natT); val kV_sp = Var(("k",0),natT);
val i_split_lemma =
  Logic.mk_implies (jT (lt ZeroC pV_sp),
    jT (mkConj (oeq (mult aV_sp kV_sp)
                    (add (mult pV_sp (rdiv (mult aV_sp kV_sp) pV_sp)) (rmod (mult aV_sp kV_sp) pV_sp)))
               (lt (rmod (mult aV_sp kV_sp) pV_sp) pV_sp)));
val r_split_lemma = checkT ("split_lemma", split_lemma, i_split_lemma);
(* soundness probe : dropping 0<p must change the statement *)
val probe_split = not ((Thm.prop_of split_lemma) aconv (jT (mkConj
      (oeq (mult aV_sp kV_sp)(add (mult pV_sp (rdiv (mult aV_sp kV_sp) pV_sp)) (rmod (mult aV_sp kV_sp) pV_sp)))
      (lt (rmod (mult aV_sp kV_sp) pV_sp) pV_sp))));

(* lar_decomp : the lar value on each branch (just re-exposing lar_lo/lar_hi on ctxtT
   in a single gated lemma to confirm both branches are usable here).
   lower : 2r<=p ==> lar a p k = r ;  upper : p<2r ==> lar a p k = p-r *)
val lar_decomp_lo =
  let
    val aF = Free("a", natT); val pF = Free("p", natT); val kF = Free("k", natT);
    val hle = Thm.assume (ctermT (jT (le (add (rOf aF pF kF)(rOf aF pF kF)) pF)));
    val eq  = lar_lo_T_at (aF, pF, kF) hle;     (* oeq (lar a p k)(rOf a p k) *)
  in varify (Thm.implies_intr (ctermT (jT (le (add (rOf aF pF kF)(rOf aF pF kF)) pF))) eq) end;
val lar_decomp_hi =
  let
    val aF = Free("a", natT); val pF = Free("p", natT); val kF = Free("k", natT);
    val hlt = Thm.assume (ctermT (jT (lt pF (add (rOf aF pF kF)(rOf aF pF kF)))));
    val eq  = lar_hi_T_at (aF, pF, kF) hlt;     (* oeq (lar a p k)(sub p (rOf a p k)) *)
  in varify (Thm.implies_intr (ctermT (jT (lt pF (add (rOf aF pF kF)(rOf aF pF kF))))) eq) end;
val i_lar_lo =
  Logic.mk_implies (jT (le (add (rOf aV_sp pV_sp kV_sp)(rOf aV_sp pV_sp kV_sp)) pV_sp),
                    jT (oeq (lar aV_sp pV_sp kV_sp) (rOf aV_sp pV_sp kV_sp)));
val i_lar_hi =
  Logic.mk_implies (jT (lt pV_sp (add (rOf aV_sp pV_sp kV_sp)(rOf aV_sp pV_sp kV_sp))),
                    jT (oeq (lar aV_sp pV_sp kV_sp) (sub pV_sp (rOf aV_sp pV_sp kV_sp))));
val r_lar_lo = checkT ("lar_decomp_lo", lar_decomp_lo, i_lar_lo);
val r_lar_hi = checkT ("lar_decomp_hi", lar_decomp_hi, i_lar_hi);

val () = if r_split_lemma andalso probe_split andalso r_lar_lo andalso r_lar_hi
         then out "EIS_SPLIT_OK\n" else out "EIS_SPLIT_FAILED\n";
val () = out "SP_SPLIT_END\n";

(* ============================================================================
   (PB-1) parity_double : parity(add z z) = 0   (any z)
   ============================================================================ *)
val () = out "PB_BEGIN\n";

val parity_double =
  let
    val zF = Free("z", natT);
    val pa = beta_norm (Drule.infer_instantiate ctxtT
               [(("a",0), ctermT zF),(("b",0), ctermT zF)] parity_add);
              (* parity(add z z) = parity(add(parity z)(parity z)) *)
    val pbz = parity_bounded_at zF;  (* Disj(parity z=0)(parity z=1) *)
    val gg = oeq (parity (add zF zF)) ZeroC;
    val cA =
      let
        val hz2 = Thm.assume (ctermT (jT (oeq (parity zF) ZeroC)))
        val w1Abs = Abs("z", natT, oeq (parity (add (parity zF)(parity zF)))
                                       (parity (add (Bound 0)(parity zF))));
        val w1 = oeq_rw_T (w1Abs, parity zF, ZeroC) hz2
                    (oeqRefl_T (parity (add (parity zF)(parity zF))));
        val w2Abs = Abs("z", natT, oeq (parity (add ZeroC (parity zF)))
                                       (parity (add ZeroC (Bound 0))));
        val w2 = oeq_rw_T (w2Abs, parity zF, ZeroC) hz2
                    (oeqRefl_T (parity (add ZeroC (parity zF))));
        val a00 = add0r_T ZeroC;  (* add 0 0 = 0 *)
        val w3Abs = Abs("z", natT, oeq (parity (add ZeroC ZeroC)) (parity (Bound 0)));
        val w3 = oeq_rw_T (w3Abs, add ZeroC ZeroC, ZeroC) a00
                    (oeqRefl_T (parity (add ZeroC ZeroC)));
        val tozero = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [pa, w1], w2],
                                     oeq_trans_T OF [w3, parity_0_T]];
      in Thm.implies_intr (ctermT (jT (oeq (parity zF) ZeroC))) tozero end;
    val cB =
      let
        val ho2 = Thm.assume (ctermT (jT (oeq (parity zF) oneC)))
        val w1Abs = Abs("z", natT, oeq (parity (add (parity zF)(parity zF)))
                                       (parity (add (Bound 0)(parity zF))));
        val w1 = oeq_rw_T (w1Abs, parity zF, oneC) ho2
                    (oeqRefl_T (parity (add (parity zF)(parity zF))));
        val w2Abs = Abs("z", natT, oeq (parity (add oneC (parity zF)))
                                       (parity (add oneC (Bound 0))));
        val w2 = oeq_rw_T (w2Abs, parity zF, oneC) ho2
                    (oeqRefl_T (parity (add oneC (parity zF))));
        val la = parityA_at (ZeroC, oneC);  (* parity(add(Suc 0)(Suc 0))=sub 1(parity(add 0 (Suc 0))) *)
        val a0l = add_0_left_T_at (suc ZeroC);  (* add 0 (Suc 0) = Suc 0 *)
        val w3Abs = Abs("z", natT, oeq (parity (add ZeroC (suc ZeroC))) (parity (Bound 0)));
        val w3 = oeq_rw_T (w3Abs, add ZeroC (suc ZeroC), suc ZeroC) a0l
                    (oeqRefl_T (parity (add ZeroC (suc ZeroC))));
        val inner = oeq_trans_T OF [w3, parity1_eq];  (* parity(add 0 (Suc 0)) = 1 *)
        val laAbs = Abs("z", natT, oeq (sub oneC (parity (add ZeroC (suc ZeroC)))) (sub oneC (Bound 0)));
        val la2 = oeq_rw_T (laAbs, parity (add ZeroC (suc ZeroC)), oneC) inner
                    (oeqRefl_T (sub oneC (parity (add ZeroC (suc ZeroC)))));
        val laFull = oeq_trans_T OF [la, oeq_trans_T OF [la2, sub1_1]];  (* = 0 *)
        val tozero = oeq_trans_T OF [oeq_trans_T OF [oeq_trans_T OF [pa, w1], w2], laFull];
      in Thm.implies_intr (ctermT (jT (oeq (parity zF) oneC))) tozero end;
  in varify (disjE_T_at (oeq (parity zF) ZeroC, oeq (parity zF) oneC, gg) pbz cA cB) end;
val zV_pd = Var(("z",0),natT);
val i_parity_double = jT (oeq (parity (add zV_pd zV_pd)) ZeroC);
val r_parity_double = checkT ("parity_double", parity_double, i_parity_double);
fun parity_double_at t = beta_norm (Drule.infer_instantiate ctxtT [(("z",0),ctermT t)] parity_double);

(* parity_odd_mult : oeq (parity a) 1 ==> oeq (parity (mult a b)) (parity b)
   (from parity_mult_l + mult_1_left + parity_idem) *)
fun parity_odd_mult_T (aT, bT) hodd =   (* hodd : oeq (parity aT) 1 *)
  let
    val pml = beta_norm (Drule.infer_instantiate ctxtT
                [(("a",0),ctermT aT),(("b",0),ctermT bT)] parity_mult_l);
              (* parity(mult a b) = parity(mult(parity a)b) *)
    (* rewrite parity a -> 1 *)
    val rAbs = Abs("z", natT, oeq (parity (mult (parity aT) bT)) (parity (mult (Bound 0) bT)));
    val r1 = oeq_rw_T (rAbs, parity aT, oneC) hodd (oeqRefl_T (parity (mult (parity aT) bT)));
             (* parity(mult(parity a)b) = parity(mult 1 b) *)
    val m1 = mult1l_T_b bT;  (* mult 1 b = b *)
    val r2Abs = Abs("z", natT, oeq (parity (mult oneC bT)) (parity (Bound 0)));
    val r2 = oeq_rw_T (r2Abs, mult oneC bT, bT) m1 (oeqRefl_T (parity (mult oneC bT)));
             (* parity(mult 1 b) = parity b *)
  in oeq_trans_T OF [pml, oeq_trans_T OF [r1, r2]] end;  (* parity(mult a b) = parity b *)

val () = if r_parity_double then out "PARITY_DOUBLE_OK\n" else out "PARITY_DOUBLE_FAILED\n";

(* ============================================================================
   (PB-2) floor_parity_link  (THE genuine new Eisenstein content, per k)
   For odd a, odd p, 0<p, p does NOT divide (a*k):
     parity (rdiv (mult a k) p) = parity (add k (rmod (mult a k) p)).
   i.e. floor(a*k/p) ≡ k + (a*k mod p)  (mod 2).
   Hypotheses kept explicit: parity a = 1, parity p = 1, 0<p.
   (p∤(a*k) is NOT needed for this parity identity — it holds from the split alone.)
   ============================================================================ *)
fun floor_parity_link_T (aT, pT, kT) hposP hoddA hoddP =
  (* hposP : lt 0 p ; hoddA : oeq (parity a) 1 ; hoddP : oeq (parity p) 1 *)
  let
    val ak = mult aT kT;
    val f  = rdiv ak pT;       (* floor *)
    val r  = rmod ak pT;       (* remainder *)
    (* split : ak = add (mult p f) r *)
    val splitC = split_lemma;  (* schematic 0<p ==> Conj(eq)(lt r p) *)
    val splitI = beta_norm (Drule.infer_instantiate ctxtT
                   [(("a",0),ctermT aT),(("p",0),ctermT pT),(("k",0),ctermT kT)] splitC);
    val splitE = Thm.implies_elim splitI hposP;  (* Conj (oeq ak (add(mult p f) r)) (lt r p) *)
    val eqSplit = conjunct1_T_at (oeq ak (add (mult pT f) r), lt r pT) splitE;
                  (* oeq ak (add (mult p f) r) *)
    (* parity(ak) = parity k   [a odd] *)
    val pAk_k = parity_odd_mult_T (aT, kT) hoddA;   (* parity(mult a k) = parity k *)
    (* parity(ak) = parity(add(mult p f) r)   [rewrite ak via eqSplit inside parity] *)
    val pSplit = let val pAbs = Abs("z", natT, oeq (parity ak) (parity (Bound 0)))
                 in oeq_rw_T (pAbs, ak, add (mult pT f) r) eqSplit (oeqRefl_T (parity ak)) end;
                 (* parity(ak) = parity(add(mult p f) r) *)
    (* parity(add(mult p f) r) = parity(add (parity(mult p f))(parity r))  [parity_add] *)
    val paMP = beta_norm (Drule.infer_instantiate ctxtT
                 [(("a",0),ctermT (mult pT f)),(("b",0),ctermT r)] parity_add);
    (* parity(mult p f) = parity f  [p odd] -> rewrite inside add (.) r in 2nd-level parity *)
    val pPf = parity_odd_mult_T (pT, f) hoddP;       (* parity(mult p f) = parity f *)
    val mpAbs = Abs("z", natT, oeq (parity (add (parity (mult pT f))(parity r)))
                                   (parity (add (Bound 0)(parity r))));
    val paMP2 = oeq_rw_T (mpAbs, parity (mult pT f), parity f) pPf
                  (oeqRefl_T (parity (add (parity (mult pT f))(parity r))));
                (* parity(add(parity(mult p f))(parity r)) = parity(add(parity f)(parity r)) *)
    (* parity(add(parity f)(parity r)) = parity(add f r)  [parity_add reversed] *)
    val paFR = beta_norm (Drule.infer_instantiate ctxtT
                 [(("a",0),ctermT f),(("b",0),ctermT r)] parity_add);
                (* parity(add f r) = parity(add(parity f)(parity r)) *)
    (* chain : parity k = parity(ak) [sym pAk_k] = parity(add(mult p f) r) [pSplit]
                = parity(add(parity(mult p f))(parity r)) [paMP]
                = parity(add(parity f)(parity r)) [paMP2]
                = parity(add f r) [paFR sym] *)
    val parK_eq_parFR =
      oeq_trans_T OF [oeq_sym_T OF [pAk_k],
        oeq_trans_T OF [pSplit,
          oeq_trans_T OF [paMP,
            oeq_trans_T OF [paMP2, oeq_sym_T OF [paFR]]]]];
      (* parity k = parity(add f r) *)
    (* GOAL : parity f = parity(add k r).  Derive parity(add k r) = parity f, then sym. *)
    (* parity(add k r) = parity(add(parity k)(parity r))  [parity_add] *)
    val pakr = beta_norm (Drule.infer_instantiate ctxtT
                 [(("a",0),ctermT kT),(("b",0),ctermT r)] parity_add);
    (* rewrite parity k -> parity(add f r) via parK_eq_parFR inside add (.) (parity r) *)
    val pakrAbs = Abs("z", natT, oeq (parity (add (parity kT)(parity r)))
                                     (parity (add (Bound 0)(parity r))));
    val pakr2 = oeq_rw_T (pakrAbs, parity kT, parity (add f r)) parK_eq_parFR
                  (oeqRefl_T (parity (add (parity kT)(parity r))));
                (* parity(add(parity k)(parity r)) = parity(add(parity(add f r))(parity r)) *)
    (* parity(add(parity(add f r))(parity r)) = parity(add (add f r) r)  [parity_add reversed, X=add f r] *)
    val paX = beta_norm (Drule.infer_instantiate ctxtT
                [(("a",0),ctermT (add f r)),(("b",0),ctermT r)] parity_add);
               (* parity(add (add f r) r) = parity(add(parity(add f r))(parity r)) *)
    (* add (add f r) r = add f (add r r)  [assoc] *)
    val assoc = addassoc_T2_at (f, r, r);   (* oeq (add(add f r)r)(add f (add r r)) *)
    (* parity(add (add f r) r) = parity(add f (add r r))  [rewrite] *)
    val passAbs = Abs("z", natT, oeq (parity (add (add f r) r)) (parity (Bound 0)));
    val pass = oeq_rw_T (passAbs, add (add f r) r, add f (add r r)) assoc
                 (oeqRefl_T (parity (add (add f r) r)));
               (* parity(add(add f r)r) = parity(add f (add r r)) *)
    (* parity(add f (add r r)) = parity(add(parity f)(parity(add r r)))  [parity_add] *)
    val paFrr = beta_norm (Drule.infer_instantiate ctxtT
                  [(("a",0),ctermT f),(("b",0),ctermT (add r r))] parity_add);
    (* parity(add r r) = 0  [parity_double] -> rewrite inside add(parity f)(.) *)
    val pdr = parity_double_at r;    (* parity(add r r) = 0 *)
    val drAbs = Abs("z", natT, oeq (parity (add (parity f)(parity (add r r))))
                                   (parity (add (parity f)(Bound 0))));
    val paFrr2 = oeq_rw_T (drAbs, parity (add r r), ZeroC) pdr
                   (oeqRefl_T (parity (add (parity f)(parity (add r r)))));
                 (* parity(add(parity f)(parity(add r r))) = parity(add(parity f) 0) *)
    (* parity(add(parity f) 0) = parity(parity f)  [add0r] = parity f [idem] *)
    val a0 = add0r_T (parity f);    (* add(parity f)0 = parity f *)
    val a0Abs = Abs("z", natT, oeq (parity (add (parity f) ZeroC)) (parity (Bound 0)));
    val a0p = oeq_rw_T (a0Abs, add (parity f) ZeroC, parity f) a0
                (oeqRefl_T (parity (add (parity f) ZeroC)));
              (* parity(add(parity f)0) = parity(parity f) *)
    val idem = beta_norm (Drule.infer_instantiate ctxtT [(("n",0),ctermT f)] parity_idem);
               (* parity(parity f) = parity f *)
    (* full : parity(add k r) = parity(add(parity k)(parity r)) [pakr]
              = parity(add(parity(add f r))(parity r)) [pakr2]
              = parity(add(add f r)r) [paX sym]
              = parity(add f (add r r)) [pass]
              = parity(add(parity f)(parity(add r r))) [paFrr]
              = parity(add(parity f)0) [paFrr2]
              = parity(parity f) [a0p]
              = parity f [idem] *)
    val pakr_eq_pf =
      oeq_trans_T OF [pakr,
        oeq_trans_T OF [pakr2,
          oeq_trans_T OF [oeq_sym_T OF [paX],
            oeq_trans_T OF [pass,
              oeq_trans_T OF [paFrr,
                oeq_trans_T OF [paFrr2,
                  oeq_trans_T OF [a0p, idem]]]]]]];
      (* parity(add k r) = parity f *)
  in oeq_sym_T OF [pakr_eq_pf] end;   (* parity f = parity(add k r) *)

(* validate floor_parity_link on concrete Frees *)
val r_floor_parity_link_partial = (* bound below by fpl_check *)
let
val fpl_check =
  let
    val aF = Free("a", natT); val pF = Free("p", natT); val kF = Free("k", natT);
    val hpos = Thm.assume (ctermT (jT (lt ZeroC pF)));
    val ha   = Thm.assume (ctermT (jT (oeq (parity aF) oneC)));
    val hp   = Thm.assume (ctermT (jT (oeq (parity pF) oneC)));
    val res  = floor_parity_link_T (aF, pF, kF) hpos ha hp;
    val intended = jT (oeq (parity (rdiv (mult aF kF) pF))
                           (parity (add kF (rmod (mult aF kF) pF))));
    val ok = (length (Thm.hyps_of res) = 3) andalso ((Thm.prop_of res) aconv intended);
  in (if ok then out "FLOOR_PARITY_LINK_OK\n"
      else (out "FLOOR_PARITY_LINK_FAILED\n";
            out ("  got = " ^ Syntax.string_of_term ctxtT (Thm.prop_of res) ^ "\n");
            out ("  int = " ^ Syntax.string_of_term ctxtT intended ^ "\n"));
      ok) end;
in fpl_check end;

(* ============================================================================
   (PB-3) parity_sumf_cong : if parity(f k) = parity(g k) for all k<=n,
   then parity(sumf f n) = parity(sumf g n).   BY INDUCTION on n.
   The agreement is carried as a META-universal premise.
   ============================================================================ *)
val fnT = natT --> natT;
val parity_sumf_cong =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    val kAg = Free("kag", natT);
    (* meta premise : !!k. le k n_free ... but n varies in induction.  We instead
       carry the STRONGER premise "agree on ALL k" : !!k. oeq(parity(f k))(parity(g k)).
       (sufficient for our use; avoids threading le k n through the induction.) *)
    val agreeProp = Logic.all kAg (jT (oeq (parity (fF $ kAg)) (parity (gF $ kAg))));
    val hAgree = Thm.assume (ctermT agreeProp);
    fun agreeAt t = Thm.forall_elim (ctermT t) hAgree;   (* oeq(parity(f t))(parity(g t)) *)
    val kF = Free("n", natT);
    val Pabs = Abs("z", natT, oeq (parity (sumf fF (Bound 0))) (parity (sumf gF (Bound 0))));
    (* BASE n=0 : parity(sumf f 0) = parity(sumf g 0) ; sumf f 0 = f 0 *)
    val baseThm =
      let
        val sf0 = sumf0_T fF;  (* sumf f 0 = f 0 *)
        val sg0 = sumf0_T gF;  (* sumf g 0 = g 0 *)
        (* parity(sumf f 0) = parity(f 0)  via rewrite *)
        val lAbs = Abs("z", natT, oeq (parity (sumf fF ZeroC)) (parity (Bound 0)));
        val l1 = oeq_rw_T (lAbs, sumf fF ZeroC, fF $ ZeroC) sf0 (oeqRefl_T (parity (sumf fF ZeroC)));
                 (* parity(sumf f 0) = parity(f 0) *)
        val ag0 = agreeAt ZeroC;  (* parity(f 0) = parity(g 0) *)
        (* parity(g 0) = parity(sumf g 0) *)
        val rAbs = Abs("z", natT, oeq (parity (sumf gF ZeroC)) (parity (Bound 0)));
        val r1 = oeq_rw_T (rAbs, sumf gF ZeroC, gF $ ZeroC) sg0 (oeqRefl_T (parity (sumf gF ZeroC)));
                 (* parity(sumf g 0) = parity(g 0) *)
      in oeq_trans_T OF [oeq_trans_T OF [l1, ag0], oeq_sym_T OF [r1]] end;
    (* STEP n -> Suc n *)
    val xF = Free("x", natT);
    val ihP = jT (oeq (parity (sumf fF xF)) (parity (sumf gF xF)));
    val IH  = Thm.assume (ctermT ihP);
    val stepConcl =
      let
        val sfS = sumfSuc_T (fF, xF);  (* sumf f (Suc x) = add (sumf f x)(f(Suc x)) *)
        val sgS = sumfSuc_T (gF, xF);  (* sumf g (Suc x) = add (sumf g x)(g(Suc x)) *)
        (* parity(sumf f (Suc x)) = parity(add(sumf f x)(f(Suc x)))  [rewrite] *)
        val lAbs = Abs("z", natT, oeq (parity (sumf fF (suc xF))) (parity (Bound 0)));
        val l1 = oeq_rw_T (lAbs, sumf fF (suc xF), add (sumf fF xF)(fF $ (suc xF))) sfS
                    (oeqRefl_T (parity (sumf fF (suc xF))));
                 (* parity(sumf f(Suc x)) = parity(add(sumf f x)(f(Suc x))) *)
        (* = parity(add(parity(sumf f x))(parity(f(Suc x))))  [parity_add] *)
        val paf = beta_norm (Drule.infer_instantiate ctxtT
                    [(("a",0),ctermT (sumf fF xF)),(("b",0),ctermT (fF $ (suc xF)))] parity_add);
        (* rewrite parity(sumf f x)->parity(sumf g x) [IH] and parity(f(Suc x))->parity(g(Suc x)) [agree] *)
        val agSx = agreeAt (suc xF);  (* parity(f(Suc x)) = parity(g(Suc x)) *)
        val m1Abs = Abs("z", natT, oeq (parity (add (parity (sumf fF xF))(parity (fF $ (suc xF)))))
                                       (parity (add (Bound 0)(parity (fF $ (suc xF))))));
        val m1 = oeq_rw_T (m1Abs, parity (sumf fF xF), parity (sumf gF xF)) IH
                    (oeqRefl_T (parity (add (parity (sumf fF xF))(parity (fF $ (suc xF))))));
                 (* = parity(add(parity(sumf g x))(parity(f(Suc x)))) *)
        val m2Abs = Abs("z", natT, oeq (parity (add (parity (sumf gF xF))(parity (fF $ (suc xF)))))
                                       (parity (add (parity (sumf gF xF))(Bound 0))));
        val m2 = oeq_rw_T (m2Abs, parity (fF $ (suc xF)), parity (gF $ (suc xF))) agSx
                    (oeqRefl_T (parity (add (parity (sumf gF xF))(parity (fF $ (suc xF))))));
                 (* = parity(add(parity(sumf g x))(parity(g(Suc x)))) *)
        (* = parity(add(sumf g x)(g(Suc x)))  [parity_add reversed] *)
        val pag = beta_norm (Drule.infer_instantiate ctxtT
                    [(("a",0),ctermT (sumf gF xF)),(("b",0),ctermT (gF $ (suc xF)))] parity_add);
                  (* parity(add(sumf g x)(g(Suc x))) = parity(add(parity(sumf g x))(parity(g(Suc x)))) *)
        (* = parity(sumf g (Suc x))  [rewrite sgS reversed] *)
        val rAbs = Abs("z", natT, oeq (parity (sumf gF (suc xF))) (parity (Bound 0)));
        val r1 = oeq_rw_T (rAbs, sumf gF (suc xF), add (sumf gF xF)(gF $ (suc xF))) sgS
                    (oeqRefl_T (parity (sumf gF (suc xF))));
                 (* parity(sumf g(Suc x)) = parity(add(sumf g x)(g(Suc x))) *)
        val chain = oeq_trans_T OF [l1, oeq_trans_T OF [paf,
                       oeq_trans_T OF [m1, oeq_trans_T OF [m2,
                         oeq_trans_T OF [oeq_sym_T OF [pag], oeq_sym_T OF [r1]]]]]];
                    (* parity(sumf f(Suc x)) = parity(sumf g(Suc x)) *)
      in chain end;
    val stepF = Thm.forall_intr (ctermT xF) (Thm.implies_intr (ctermT ihP) stepConcl);
    val run = nat_induct_T_run Pabs kF baseThm stepF;
    val d1 = Thm.implies_intr (ctermT agreeProp) run;
  in varify d1 end;
val fV_psc = Var(("f",0),fnT); val gV_psc = Var(("g",0),fnT); val nV_psc = Var(("n",0),natT);
val kV_psc = Free("kag",natT);
val i_parity_sumf_cong =
  Logic.mk_implies (
    Logic.all kV_psc (jT (oeq (parity (fV_psc $ kV_psc)) (parity (gV_psc $ kV_psc)))),
    jT (oeq (parity (sumf fV_psc nV_psc)) (parity (sumf gV_psc nV_psc))));
val r_parity_sumf_cong = checkT ("parity_sumf_cong", parity_sumf_cong, i_parity_sumf_cong);
val () = if r_parity_sumf_cong then out "PARITY_SUMF_CONG_OK\n" else out "PARITY_SUMF_CONG_FAILED\n";

val () = out "PB_CHECKPOINT_1\n";

(* ============================================================================
   (PB-4) floor_sum_kr_parity  (HALF of the Eisenstein parity bookkeeping)
   For odd q, odd p, 0<p :
     parity (sumf (\k. rdiv (mult q k) p) m)
       = parity (add (sumf (\k. k) m) (sumf (\k. rmod (mult q k) p) m)).
   i.e.  sum_{k} floor(q*k/p)  ==  (sum_{k} k) + (sum_{k} q*k mod p)   (mod 2).
   PROOF: per-k floor_parity_link gives parity(floor k)=parity(add k (rmod k)) for
   ALL k (incl 0, where both sides are 0); parity_sumf_cong lifts to the sum;
   sum_add collapses sumf(%k. add k (rmod k)) = add(sumf id)(sumf rmod); parity_add.
   ============================================================================ *)
val () = out "PB2_BEGIN\n";

(* abstractions (eta-explicit, FRESH Free, capture-safe) *)
val idAbs   = let val zk = Free("k_id", natT) in Term.lambda zk zk end;            (* %k. k *)
fun floorAbsT q p = let val zk = Free("k_fa", natT) in Term.lambda zk (rdiv (mult q zk) p) end;
fun rmodAbsT  q p = let val zk = Free("k_ra", natT) in Term.lambda zk (rmod (mult q zk) p) end;
fun krAbsT    q p = let val zk = Free("k_kr", natT) in Term.lambda zk (add zk (rmod (mult q zk) p)) end;

(* sum_add / sum_mult_l ground instantiators on ctxtT *)
fun sum_add_T_at (fT, gT, nt) = beta_norm (Drule.infer_instantiate ctxtT
      [(("f",0),ctermT fT),(("g",0),ctermT gT),(("n",0),ctermT nt)] sum_add_T);

val floor_sum_kr_parity =
  let
    val qF = Free("q", natT); val pF = Free("p", natT); val mF = Free("m", natT);
    val hpos = Thm.assume (ctermT (jT (lt ZeroC pF)));
    val hoddQ = Thm.assume (ctermT (jT (oeq (parity qF) oneC)));
    val hoddP = Thm.assume (ctermT (jT (oeq (parity pF) oneC)));
    val flA = floorAbsT qF pF;     (* %k. rdiv(q*k)p *)
    val krA = krAbsT qF pF;        (* %k. add k (rmod(q*k)p) *)
    val rmA = rmodAbsT qF pF;      (* %k. rmod(q*k)p *)
    (* STEP 1 : parity(sumf flA m) = parity(sumf krA m)  via parity_sumf_cong
       need agreement : !!k. oeq (parity (flA$k)) (parity (krA$k))
       = oeq (parity(rdiv(q*k)p)) (parity(add k (rmod(q*k)p)))  -- floor_parity_link *)
    val kAg = Free("kag", natT);
    val agreeBody = jT (oeq (parity (rdiv (mult qF kAg) pF))
                            (parity (add kAg (rmod (mult qF kAg) pF))));
    val agreeThm = floor_parity_link_T (qF, pF, kAg) hpos hoddQ hoddP;  (* the body, 3 free hyps already discharged *)
    (* agreeThm : oeq (parity(rdiv(q*kag)p))(parity(add kag (rmod(q*kag)p)))  with hyps closed by assume *)
    val agreeMeta = Thm.forall_intr (ctermT kAg) agreeThm;  (* !!kag. <body> *)
    (* parity_sumf_cong instance : f:=flA, g:=krA *)
    val pscI = beta_norm (Drule.infer_instantiate ctxtT
                 [(("f",0),ctermT flA),(("g",0),ctermT krA),(("n",0),ctermT mF)] parity_sumf_cong);
    (* pscI : (!!kag. oeq(parity(flA kag))(parity(krA kag))) ==> oeq(parity(sumf flA m))(parity(sumf krA m))
       beta-reduce the lambda applications inside the premise to match agreeMeta *)
    val step1 = Thm.implies_elim pscI agreeMeta;
                (* oeq (parity(sumf flA m))(parity(sumf krA m)) *)
    (* STEP 2 : sumf krA m = add (sumf idAbs m)(sumf rmA m)  via sum_add (reversed)
       sum_add_T_at(idAbs, rmA, m) : oeq (add(sumf idAbs m)(sumf rmA m))(sumf (%k. add(idAbs k)(rmA k)) m)
       and (%k. add(idAbs k)(rmA k)) beta-eq krA *)
    val sa = sum_add_T_at (idAbs, rmA, mF);
             (* oeq (add(sumf idAbs m)(sumf rmA m)) (sumf (%k. add(idAbs$k)(rmA$k)) m) *)
    (* the RHS abstraction of sa is (%k. add (idAbs$k)(rmA$k)); beta-reduces to krA.  Both are
       beta-equal so aconv-after-beta; we use sa REVERSED then rewrite parity(sumf krA m). *)
    val saSym = oeq_sym_T OF [sa];
                (* oeq (sumf (%k. add(idAbs$k)(rmA$k)) m) (add(sumf idAbs m)(sumf rmA m)) *)
    (* rewrite parity(sumf krA m) : note sumf krA m and sumf (%k. add(idAbs$k)(rmA$k)) m are
       beta-equal terms.  beta_norm sa to align. *)
    val sa_b = beta_norm sa;
    val saSym_b = beta_norm saSym;
    (* parity(sumf krA m) -> parity(add(sumf idAbs m)(sumf rmA m)) *)
    val rwAbs = Abs("z", natT, oeq (parity (sumf krA mF)) (parity (Bound 0)));
    val step2 = oeq_rw_T (rwAbs, sumf krA mF, add (sumf idAbs mF)(sumf rmA mF)) saSym_b
                  (oeqRefl_T (parity (sumf krA mF)));
                (* parity(sumf krA m) = parity(add(sumf idAbs m)(sumf rmA m)) *)
    val res = oeq_trans_T OF [step1, step2];
              (* parity(sumf flA m) = parity(add(sumf idAbs m)(sumf rmA m)) *)
    val d3 = Thm.implies_intr (ctermT (jT (oeq (parity pF) oneC))) res;
    val d2 = Thm.implies_intr (ctermT (jT (oeq (parity qF) oneC))) d3;
    val d1 = Thm.implies_intr (ctermT (jT (lt ZeroC pF))) d2;
  in varify d1 end;
(* validate *)
val qV_fs = Var(("q",0),natT); val pV_fs = Var(("p",0),natT); val mV_fs = Var(("m",0),natT);
val flAv = let val zk = Free("k_fa", natT) in Term.lambda zk (rdiv (mult qV_fs zk) pV_fs) end;
val idAv = let val zk = Free("k_id", natT) in Term.lambda zk zk end;
val rmAv = let val zk = Free("k_ra", natT) in Term.lambda zk (rmod (mult qV_fs zk) pV_fs) end;
val i_floor_sum_kr_parity =
  Logic.mk_implies (jT (lt ZeroC pV_fs),
    Logic.mk_implies (jT (oeq (parity qV_fs) oneC),
      Logic.mk_implies (jT (oeq (parity pV_fs) oneC),
        jT (oeq (parity (sumf flAv mV_fs))
                (parity (add (sumf idAv mV_fs) (sumf rmAv mV_fs)))))));
val r_floor_sum_kr_parity =
  let val ok = (length (Thm.hyps_of floor_sum_kr_parity) = 0)
               andalso (length (Thm.extra_shyps floor_sum_kr_parity) = 0)
               andalso ((Thm.prop_of floor_sum_kr_parity) aconv i_floor_sum_kr_parity)
  in (if ok then out "OK floor_sum_kr_parity\n"
      else (out "FAIL floor_sum_kr_parity\n";
            out ("  got = " ^ Syntax.string_of_term ctxtT (Thm.prop_of floor_sum_kr_parity) ^ "\n");
            out ("  int = " ^ Syntax.string_of_term ctxtT i_floor_sum_kr_parity ^ "\n"));
      ok) end;
val () = if r_floor_sum_kr_parity then out "FLOOR_SUM_KR_PARITY_OK\n" else out "FLOOR_SUM_KR_PARITY_FAILED\n";
val () = out "PB2_END\n";

(* ============================================================================
   (PB)  PARITY BRIDGE  --  STATUS
   ----------------------------------------------------------------------------
   BANKED (all 0-hyp-mod-stated-premises + aconv):
     * floor_parity_link  : parity(floor(q*k/p)) = parity(k + (q*k mod p))      [per k, THE analytic crux]
     * floor_sum_kr_parity: parity(sum floor) = parity((sum k) + (sum (q*k mod p)))  [HALF the bookkeeping]
     * parity_sumf_cong, parity_double, parity_mult_l, parity_odd_mult, sum_const
   BLOCKED  (the remaining half : sum r == sum k + mu  (mod 2)):
     This needs the SUM-permutation invariance of the least-absolute-residue map
     (sum_{k=1..m} lar(q*k) = sum_{k=1..m} k), because
       sum r_k = sum lar_k + mu*p - 2*(sum of flipped lar_k)  ==>  sum r == sum k + mu (mod 2).
     The tower banks LAR_PERM only as a PRODUCT invariant (lprod over the natlist);
     there is NO list-SUM (lsumf) and NO sum-reindex/sum-permutation lemma anywhere.
     Re-deriving lar's permutation as a SUM is fresh infrastructure (a parallel
     lsumf + its permutation invariance) -- a separate fleet.  Hence the FULL
     eisenstein_parity (mu == sum floor mod 2) is NOT closed here.
   ============================================================================ *)
val eisParityFull = false;   (* honest: the full mu == sum floor (mod 2) is NOT proved *)
val () = if r_floor_parity_link_partial andalso r_floor_sum_kr_parity
         then out "EIS_PARITY_PARTIAL_OK\n" else out "EIS_PARITY_PARTIAL_INCOMPLETE\n";

(* ============================================================================
   (EL)  EISENSTEIN LEMMA  --  STATUS
   The deliverable legendre(q,p) = (-1)^(sum floor) = (-1)^mu  follows from
   gauss_lemma (S = (-1)^mu, ALREADY proved) THE MOMENT  mu == sum floor (mod 2)
   is available.  Since that parity equality is blocked (above), the Eisenstein
   lemma is NOT closed here.  What IS in hand:
     * gauss_lemma (S in {1,p-1}, S = (-1)^mu)  -- on ctxtGG, re-usable on ctxtT
     * the full per-k + half-sum parity bridge above.
   ============================================================================ *)
val eisLemmaFull = false;
val () = out "EIS_LEMMA_PARTIAL_NOTE\n";

(* ============================================================================
   SOUNDNESS  +  AXIOM AUDIT  (the F2 delta)
   Every banked F2 lemma is 0-hyp (mod its stated premises) + aconv; NO new axiom
   beyond the 5 conservative-recursion axioms (parity/cnt) the toolbox already
   declared; the ONLY classical axiom is ex_middle; NOTHING fabricated.
   ============================================================================ *)
val () = out "F2_AUDIT_BEGIN\n";
val allAxF2 = Theory.all_axioms_of thyT;
val () = out ("f2_axiom_count=" ^ Int.toString (length allAxF2) ^ "\n");
val hasEMf2 = List.exists (fn (nm,_) => String.isSuffix "ex_middle" nm orelse nm = "ex_middle") allAxF2;
val () = out ("f2_ex_middle_present=" ^ Bool.toString hasEMf2 ^ "\n");
(* assert NO fabricated eisenstein/legendre/reciprocity/parity-bridge axiom *)
val bad = List.filter (fn nm => let val l = String.map Char.toLower nm in
              String.isSubstring "eisenstein" l orelse String.isSubstring "legendre" l
              orelse String.isSubstring "reciprocity" l orelse String.isSubstring "lattice" l
              orelse String.isSubstring "floor_parity" l orelse String.isSubstring "muSum" l end)
            (map fst allAxF2);
val () = out ("f2_fabricated_axioms=[" ^ String.concatWith "," bad ^ "]\n");
(* enumerate the new (toolbox) axioms again -- must be exactly the 5 cnt/parity ones *)
val newAxF2 = List.filter (fn nm => let val l = String.map Char.toLower nm in
                  String.isSubstring "parity" l orelse String.isSubstring "cnt" l end)
                (map fst allAxF2);
val () = out ("f2_recursion_axioms=[" ^ String.concatWith "," newAxF2 ^ "]\n");
val () = out "F2_AUDIT_END\n";

(* ---- master gate ---- *)
val f2AllOK = r_parity_mult_l andalso r_parity_double andalso r_floor_parity_link_partial
              andalso r_split_lemma andalso r_lar_lo andalso r_lar_hi
              andalso r_parity_sumf_cong andalso r_floor_sum_kr_parity
              andalso hasEMf2 andalso (bad = []);
val () = if f2AllOK then out "QR_F2_ALL_OK\n" else out "QR_F2_PARTIAL\n";
val () = out "EISENSTEIN_BRIDGE_END\n";
