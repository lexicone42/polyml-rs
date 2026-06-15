(* ============================================================================
   CLASSIC COMBINATORIAL IDENTITIES in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_combinatorics.rs)
   ----------------------------------------------------------------------------
   Three famous binomial-coefficient identities, each a 0-hypothesis theorem by
   genuine LCF kernel inference, on top of the binomial-theorem development
   (binom + Pascal, the higher-order finite sum sumf, the sum-algebra, pow):

     pascal_row_sum : |- sumf (%k. binom n k) n = pow 2 n
                      C(n,0)+C(n,1)+...+C(n,n) = 2^n -- the row sum of Pascal's
                      triangle. Proved as a COROLLARY of binom_theorem at a=b=1
                      (pow_one_base collapses 1^k, sum_cong tidies the summand).
     hockey_stick   : |- sumf (%i. binom i r) n = binom (Suc n) (Suc r)
                      C(0,r)+C(1,r)+...+C(n,r) = C(n+1, r+1) -- the hockey-stick
                      identity, by induction on n + Pascal.
     vandermonde    : |- sumf (%j. binom m j * binom n (k - j)) k = binom (m+n) k
                      sum_{j=0..k} C(m,j) C(n,k-j) = C(m+n, k) -- Vandermonde's
                      identity (the capstone), by induction with the classic
                      Pascal-split + reindex + recombine.

   Built on the binomial-theorem development (isabelle_binom_thm.sml) over the
   classical foundation, spliced in by common::with_binom_thm. Each identity
   carries a soundness probe. Proved by a multi-seat ultracode fleet racing all
   three concurrently (wf_bd77c82b-594); re-verified end-to-end by hand.
   ============================================================================ *)

(* ============================================================================
   PASCAL'S ROW SUM :  sumf (%k. binom n k) n = pow (Suc (Suc Zero)) n
   i.e.  C(n,0)+C(n,1)+...+C(n,n) = 2^n.
   Corollary of the binomial theorem at a:=1, b:=1.
   ============================================================================ *)
val () = out "PASCAL_BEGIN\n";

(* --- pow_one_base : pow (Suc Zero) m = Suc Zero  (a^... where a=1)  by induction on m --- *)
val pow_one_base =
  let
    val oneC = suc ZeroC;
    fun pbody zt = oeq (pow oneC zt) (suc ZeroC);
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (pbody zV);
    val mIndV = Free("m", natT);
    val ind = nat_induct_atS2 (Qpred, mIndV);
    (* BASE m=0 :  pow 1 0 = Suc 0  [pow_Zero] *)
    val base = powZeroS2_at oneC;                          (* pow 1 0 = Suc 0 *)
    (* STEP : IH pow 1 x = Suc 0  ==>  pow 1 (Suc x) = Suc 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (pbody xF);
    val IH = Thm.assume (ctermSub ihprop);                 (* pow 1 x = Suc 0 *)
    val pSuc = powSucS2_at (oneC, xF);                     (* pow 1 (Suc x) = mult 1 (pow 1 x) *)
    val cIH  = mult_cong_rS2 (oneC, pow oneC xF, suc ZeroC) IH;  (* mult 1 (pow 1 x) = mult 1 (Suc 0) *)
    val m1l  = mult1lS2_at (suc ZeroC);                    (* mult 1 (Suc 0) = Suc 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [pSuc, cIH], m1l];  (* pow 1 (Suc x) = Suc 0 *)
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val pow_one_base_v = pow_one_base;   (* already schematic: ?m *)
fun powOneBase_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("m",0), ctermSub t)] pow_one_base_v);
val () = out "POW_ONE_BASE_OK\n";

(* --- THE COROLLARY : pascal_row_sum --- *)
val pascal_row_sum =
  let
    val oneC = suc ZeroC;
    val nF   = Free("n", natT);
    (* instantiate binom_theorem at a:=1, b:=1, n:=n  (binom_theorem is schematic ?a ?b ?n) *)
    val bt = beta_norm (Drule.infer_instantiate ctxtSub
              [(("a",0), ctermSub oneC),(("b",0), ctermSub oneC),(("n",0), ctermSub nF)] binom_theorem);
    (* bt :  pow (add 1 1) n  =  sumf (%k. C(n,k)*(1^k * 1^(n-k))) n *)

    (* RHS source summand abs (exactly the binom_theorem RHS body at a=b=1) *)
    val Fsrc = Abs("k", natT,
          mult (binom nF (Bound 0)) (mult (pow oneC (Bound 0)) (pow oneC (sub nF (Bound 0)))));
    (* RHS target summand abs : %k. binom n k *)
    val Gtgt = Abs("k", natT, binom nF (Bound 0));

    (* congProof : !!k. le k n ==> Fsrc_at k = Gtgt_at k *)
    val congSum =
      let
        val kF = Free("k", natT);
        (* mult (pow 1 k)(pow 1 (n-k)) = mult 1 1 = 1 *)
        val p1k  = powOneBase_at kF;                              (* pow 1 k = Suc 0 *)
        val p1nk = powOneBase_at (sub nF kF);                     (* pow 1 (n-k) = Suc 0 *)
        val innL = mult_cong_lS2 (pow oneC kF, suc ZeroC, pow oneC (sub nF kF)) p1k;
                   (* mult (pow 1 k)(pow 1 (n-k)) = mult 1 (pow 1 (n-k)) *)
        val innR = mult_cong_rS2 (suc ZeroC, pow oneC (sub nF kF), suc ZeroC) p1nk;
                   (* mult 1 (pow 1 (n-k)) = mult 1 1 *)
        val inn1 = oeq_trans OF [innL, innR];                     (* = mult 1 1 *)
        val m11  = mult1lS2_at (suc ZeroC);                       (* mult 1 1 = Suc 0 *)
        val inner = oeq_trans OF [inn1, m11];                     (* mult(pow..)(pow..) = Suc 0 *)
        (* outer : mult (C(n,k)) (mult(..)(..)) = mult (C(n,k)) 1 = C(n,k) *)
        val outerC = mult_cong_rS2 (binom nF kF, mult (pow oneC kF) (pow oneC (sub nF kF)), suc ZeroC) inner;
                     (* = mult (C(n,k)) (Suc 0) *)
        val cm   = multcommS2_at (binom nF kF, suc ZeroC);        (* mult C 1 = mult 1 C *)
        val m1lC = mult1lS2_at (binom nF kF);                     (* mult 1 C = C *)
        val outer = oeq_trans OF [oeq_trans OF [outerC, cm], m1lC];  (* Fsrc_at k = C(n,k) = Gtgt_at k *)
        val dis = Thm.implies_intr (ctermSub (jT (le kF nF))) outer;
        val allm = Thm.forall_intr (ctermSub kF) dis;            (* !!k. le k n ==> Fsrc_at k = Gtgt_at k *)
      in sum_cong_at (Fsrc, Gtgt, nF) allm end;                  (* sumf Fsrc n = sumf Gtgt n *)

    (* RHS chain : bt-RHS = sumf Fsrc n  --(congSum)-->  sumf Gtgt n *)
    val rhsEq = congSum;                                          (* sumf Fsrc n = sumf Gtgt n *)

    (* LHS : pow (add 1 1) n = pow (Suc(Suc Zero)) n.
       add 1 1 = Suc(add 0 1) = Suc(Suc 0).  *)
    val a11   = addSucS2_at (ZeroC, oneC);                        (* add (Suc 0) (Suc 0) = Suc (add 0 (Suc 0)) *)
    val a01   = add0S2_at oneC;                                   (* add 0 (Suc 0) = Suc 0 *)
    val a01s  = Suc_cong OF [a01];                                (* Suc (add 0 (Suc 0)) = Suc (Suc 0) *)
    val addEq = oeq_trans OF [a11, a01s];                         (* add 1 1 = Suc (Suc 0) *)
    (* pow first-arg congruence : add 1 1 = Suc(Suc 0)  ==> pow (add 1 1) n = pow (Suc(Suc 0)) n *)
    val powLhsEq =
      let
        val twoC = suc (suc ZeroC);
        val Pabs = Abs("z", natT, oeq (pow (add oneC oneC) nF) (pow (Bound 0) nF));
        val inst = beta_norm (Drule.infer_instantiate ctxtSub
              [(("P",0), ctermSub Pabs), (("a",0), ctermSub (add oneC oneC)), (("b",0), ctermSub twoC)] oeq_subst_vS2);
        val refl = beta_norm (Drule.infer_instantiate ctxtSub
              [(("a",0), ctermSub (pow (add oneC oneC) nF))] oeq_refl_vS2);
      in inst OF [addEq, refl] end;                               (* pow (add 1 1) n = pow (Suc(Suc 0)) n *)

    (* CHAIN :  pow (Suc(Suc 0)) n  = pow (add 1 1) n  [sym powLhsEq]
                                   = sumf Fsrc n        [sym bt]
                                   = sumf Gtgt n        [rhsEq]
       i.e. final goal : sumf Gtgt n = pow (Suc(Suc 0)) n.
       Build it as : sumf Fsrc n = pow (Suc(Suc 0)) n  via sym, then prepend rhsEq. *)
    val btsym   = oeq_sym OF [bt];                               (* sumf Fsrc n = pow (add 1 1) n *)
    val mid     = oeq_trans OF [btsym, powLhsEq];                (* sumf Fsrc n = pow (Suc(Suc 0)) n *)
    val rhsEqs  = oeq_sym OF [rhsEq];                            (* sumf Gtgt n = sumf Fsrc n *)
    val finalEq = oeq_trans OF [rhsEqs, mid];                    (* sumf Gtgt n = pow (Suc(Suc 0)) n *)
  in varify finalEq end;

val () = out "OK pascal_row_sum\n";

(* --- SOUNDNESS PROBE : the proved thm is aconv the intended statement;
       and the kernel rejects replacing 2 (Suc(Suc Zero)) by 3.
       NB: varify eta-contracts the summand %k. binom n k  ->  binom n, so the
       intended uses the eta-contracted form binomC $ nVp to match aconv. --- *)
val i_pascal_row_sum =
  let
    val nVp = Var (("n",0), natT);
    val Gv  = binomC $ nVp                   (* eta-contracted  %k. binom n k *)
  in jT (oeq (sumf Gv nVp) (pow (suc (suc ZeroC)) nVp)) end;
val r_pascal_row_sum = checkSub ("pascal_row_sum", pascal_row_sum, i_pascal_row_sum);

(* negative probe : intended-with-3 must NOT be aconv to the real theorem *)
val i_pascal_wrong =
  let
    val nVp = Var (("n",0), natT);
    val Gv  = binomC $ nVp
  in jT (oeq (sumf Gv nVp) (pow (suc (suc (suc ZeroC))) nVp)) end;
val r_wrong_rejected = not ((Thm.prop_of pascal_row_sum) aconv i_pascal_wrong);

val () =
  if r_pascal_row_sum andalso r_wrong_rejected
  then out "PASCAL_ROW_SUM_OK\n"
  else out "PASCAL_ROW_SUM_FAILED\n";


(* ============================================================================
   ***  THE HOCKEY STICK IDENTITY  ***
   ----------------------------------------------------------------------------
   hockey_stick :
     oeq (sumf (Abs i. binom i r) n)  (binom (Suc n) (Suc r))
   i.e.  C(0,r)+C(1,r)+...+C(n,r)  =  C(n+1, r+1)    (for all r, all n).
   Proof by induction on n with r FREE.  The summand (Abs i. binom i r) does
   NOT depend on the induction variable, so no sum_cong is needed -- only
   sumf_0 / sumf_Suc + Pascal (binom_Suc_Suc) + binom_0_Suc + add_0_right +
   add_comm.  All on ctxtSub.
   ============================================================================ *)

val () = out "HOCKEY_BEGIN\n";

val hockey_stick =
  let
    val rF = Free("r", natT);
    (* the constant-in-n summand : %i. binom i r *)
    val Fcol = Abs("i", natT, binom (Bound 0) rF);

    (* predicate P z = oeq (sumf Fcol z) (binom (Suc z)(Suc r)) *)
    val Qpred = Abs("z", natT, oeq (sumf Fcol (Bound 0)) (binom (suc (Bound 0)) (suc rF)));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ====================================================================
       BASE  n = 0 :  sumf Fcol 0 = binom 0 r ;  RHS = binom (Suc 0)(Suc r).
         binom (Suc 0)(Suc r) = add (binom 0 r)(binom 0 (Suc r))  [Pascal]
                              = add (binom 0 r) 0                  [binom_0_Suc]
                              = binom 0 r                          [add_0_right]
       ==================================================================== *)
    val base =
      let
        val sf0   = sumf0_at Fcol;                          (* sumf Fcol 0 = binom 0 r  (beta) *)
        val pasc0 = binomSSS2_at (ZeroC, rF);              (* binom (Suc 0)(Suc r) = add (binom 0 r)(binom 0 (Suc r)) *)
        val b0S   = binom0SS2_at rF;                       (* binom 0 (Suc r) = 0 *)
        val crR   = add_cong_rS2 (binom ZeroC rF, binom ZeroC (suc rF), ZeroC) b0S;
                    (* add (binom 0 r)(binom 0 (Suc r)) = add (binom 0 r) 0 *)
        val a0r   = add0rS2_at (binom ZeroC rF);           (* add (binom 0 r) 0 = binom 0 r *)
        val rhsChain = oeq_trans OF [oeq_trans OF [pasc0, crR], a0r];
                    (* binom (Suc 0)(Suc r) = binom 0 r *)
        val rhsSym = oeq_sym OF [rhsChain];               (* binom 0 r = binom (Suc 0)(Suc r) *)
      in oeq_trans OF [sf0, rhsSym] end;                   (* sumf Fcol 0 = binom (Suc 0)(Suc r) *)

    (* ====================================================================
       STEP  x -> Suc x.   IH : sumf Fcol x = binom (Suc x)(Suc r).
         sumf Fcol (Suc x) = add (sumf Fcol x)(binom (Suc x) r)        [sumf_Suc, beta]
                           = add (binom (Suc x)(Suc r))(binom (Suc x) r)  [IH, cong_l]
                           = add (binom (Suc x) r)(binom (Suc x)(Suc r))  [add_comm]
                           = binom (Suc (Suc x))(Suc r)                   [Pascal sym]
       ==================================================================== *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf Fcol xF) (binom (suc xF) (suc rF)));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val sfS  = sumfSuc_at (Fcol, xF);
                   (* sumf Fcol (Suc x) = add (sumf Fcol x)(binom (Suc x) r)   (beta of Fcol $ (Suc x)) *)
        val cL   = add_cong_lS2 (sumf Fcol xF, binom (suc xF) (suc rF), binom (suc xF) rF) IH;
                   (* add (sumf Fcol x)(binom (Suc x) r)
                        = add (binom (Suc x)(Suc r))(binom (Suc x) r) *)
        val cm   = addcommS2_at (binom (suc xF) (suc rF), binom (suc xF) rF);
                   (* add (binom (Suc x)(Suc r))(binom (Suc x) r)
                        = add (binom (Suc x) r)(binom (Suc x)(Suc r)) *)
        val pasc = binomSSS2_at (suc xF, rF);
                   (* binom (Suc (Suc x))(Suc r)
                        = add (binom (Suc x) r)(binom (Suc x)(Suc r)) *)
        val pascSym = oeq_sym OF [pasc];
                   (* add (binom (Suc x) r)(binom (Suc x)(Suc r))
                        = binom (Suc (Suc x))(Suc r) *)
      in oeq_trans OF [oeq_trans OF [oeq_trans OF [sfS, cL], cm], pascSym] end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* intended schematic statement on ctxtSub *)
val rVs = Var (("r",0), natT);
val FcolVs = Abs("i", natT, binom (Bound 0) rVs);
val i_hockey_stick = jT (oeq (sumf FcolVs nVs) (binom (suc nVs) (suc rVs)));
val r_hockey_stick = checkSub ("hockey_stick", hockey_stick, i_hockey_stick);

(* ---- SOUNDNESS PROBE : the kernel must REJECT a false off-by-one variant.
        Claim  sumf (%i. binom i r) n = binom n (Suc r)  (drop the +1 on n).
        We only ASSERT that the true statement is NOT aconv the false one. ---- *)
val i_hockey_false = jT (oeq (sumf FcolVs nVs) (binom nVs (suc rVs)));
val s_hockey_sound =
  not ((Thm.prop_of hockey_stick) aconv i_hockey_false);

val () =
  if r_hockey_stick andalso s_hockey_sound
  then out "OK hockey_stick\nHOCKEY_STICK_OK\n"
  else out "HOCKEY_STICK_FAIL\n";

(* ============================================================================
   VANDERMONDE'S IDENTITY
     sumf (%j. binom m j * binom n (k - j)) k  =  binom (add m n) k
   Induction on m, with k object-universally quantified (n also generalised).
   ============================================================================ *)
val () = out "VAND_BEGIN\n";

(* ---- case-split machinery on ctxtSub ---- *)
val disjE_vS2 = varify disjE_ax;
val dzos_vS2  = varify disj_zero_or_suc;
fun disjE_elimS2 (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("A",0), ctermSub At), (("B",0), ctermSub Bt), (("C",0), ctermSub Ct)] disjE_vS2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun dzos_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("p",0), ctermSub t)] dzos_vS2);

(* ---- mult_0 instantiator : mult 0 t = 0 ---- *)
val mult_0_vS2 = varify mult_0;
fun mult0lS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_vS2);

val nF0 = Free("n", natT);    (* the (eventually generalised) n for the whole development *)

(* ============================================================================
   HELPER  sum_zero : Forall q. sumf (%j. Zero) q = Zero
   ============================================================================ *)
val zeroAbs = Abs("j", natT, ZeroC);   (* %j. 0 *)
val sum_zero =
  let
    val Qpred = Abs("z", natT, oeq (sumf zeroAbs (Bound 0)) ZeroC);
    val qF = Free("q", natT);
    val ind = nat_induct_atS2 (Qpred, qF);
    val base = sumf0_at zeroAbs;     (* sumf zeroAbs 0 = 0  (beta) *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf zeroAbs xF) ZeroC);
    val IH = Thm.assume (ctermSub ihprop);
    val sfS = sumfSuc_at (zeroAbs, xF);   (* sumf zeroAbs (Sx) = add (sumf zeroAbs x)(zeroAbs $ Sx) *)
    val cL = add_cong_lS2 (sumf zeroAbs xF, ZeroC, ZeroC) IH;  (* add (sumf zeroAbs x) 0 = add 0 0 *)
    val a00 = add0S2_at ZeroC;            (* add 0 0 = 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [sfS, cL], a00];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val sum_zero_vS2 = varify sum_zero;
fun sum_zero_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("q",0), ctermSub t)] sum_zero_vS2);

val qVs = Var (("q",0), natT);
val i_sum_zero = jT (oeq (sumf zeroAbs qVs) ZeroC);
val r_sum_zero = checkSub ("sum_zero", sum_zero, i_sum_zero);

(* sum_cong on ctxtSub (copy from binom_theorem) *)
val sum_cong_vS2 = varify sum_cong;
fun sum_cong_at (fAbs, gAbs, nt) congProof =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("f",0), ctermSub fAbs), (("g",0), ctermSub gAbs), (("n",0), ctermSub nt)] sum_cong_vS2)
  in Thm.implies_elim inst congProof end;

val () = out "VAND_HELPERS_OK\n";

(* binom LEFT-arg congruence on ctxtSub : oeq u v ==> oeq (binom u k)(binom v k) *)
fun binom_cong_l2 (kT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (binom uT kT) (binom (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub uT), (("b",0), ctermSub vT)] oeq_subst_vS2);
    val refl_uk = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (binom uT kT))] oeq_refl_vS2);
  in inst OF [huv, refl_uk] end;

(* ============================================================================
   THE MAIN INDUCTION (on m)
   ============================================================================ *)
val vandermonde =
  let
    val kFV = Free("k", natT);
    fun vsAbs mt kt = Abs("j", natT, mult (binom mt (Bound 0)) (binom nF0 (sub kt (Bound 0))));
    fun vbody mt kt = oeq (sumf (vsAbs mt kt) kt) (binom (add mt nF0) kt);
    fun predAbs mt = Term.lambda kFV (vbody mt kFV);
    fun predForall mt = mkForall (predAbs mt);

    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (predForall zV);
    val mIndV = Free("m", natT);
    val ind = nat_induct_atS2 (Qpred, mIndV);

    (* ====================================================================
       BASE m = 0 :  Forall k. sumf (vsAbs 0 k) k = binom (add 0 n) k
       ==================================================================== *)
    val base =
      let
        val kF = Free("k", natT);
        val dz = dzos_at kF;
        val goalC = vbody ZeroC kF;

        val caseA =
          let
            val hA = jT (oeq kF ZeroC);
            val sf0 = sumf0_at (vsAbs ZeroC ZeroC);
            val b00 = binomN0S2_at ZeroC;
            val cL  = mult_cong_lS2 (binom ZeroC ZeroC, suc ZeroC, binom nF0 (sub ZeroC ZeroC)) b00;
            val m1l = mult1lS2_at (binom nF0 (sub ZeroC ZeroC));
            val s00 = subN0S2_at ZeroC;
            val bcr = binom_cong_r2 (nF0, sub ZeroC ZeroC, ZeroC) s00;
            val lhs = oeq_trans OF [oeq_trans OF [oeq_trans OF [sf0, cL], m1l], bcr];
            val a0n = add0S2_at nF0;
            val rhsC = binom_cong_l2 (ZeroC, add ZeroC nF0, nF0) a0n;
            val rhsCs= oeq_sym OF [rhsC];
            val vbody00 = oeq_trans OF [lhs, rhsCs];
            val hAthm = Thm.assume (ctermSub hA);
            val hAsym = oeq_sym OF [hAthm];
            val transported = substPredS2 (predAbs ZeroC, ZeroC, kF) hAsym vbody00;
            val dis = Thm.implies_intr (ctermSub hA) transported;
          in dis end;

        val exTerm = mkExSuc kF;
        val caseB =
          let
            val hB = jT exTerm;
            val PabsE = Abs("q", natT, oeq kF (suc (Bound 0)));
            fun bodyFn qF hqThm =
              let
                val Fsq = vsAbs ZeroC (suc qF);
                val peel = beta_norm (Drule.infer_instantiate ctxtSub
                      [(("f",0), ctermSub Fsq), (("n",0), ctermSub qF)] sum_peel_first);
                val Fsq0red = mult (binom ZeroC ZeroC) (binom nF0 (sub (suc qF) ZeroC));
                val F0_reduce =
                  let
                    val b00 = binomN0S2_at ZeroC;
                    val cL  = mult_cong_lS2 (binom ZeroC ZeroC, suc ZeroC, binom nF0 (sub (suc qF) ZeroC)) b00;
                    val m1l = mult1lS2_at (binom nF0 (sub (suc qF) ZeroC));
                    val ssq0= subN0S2_at (suc qF);
                    val bcr = binom_cong_r2 (nF0, sub (suc qF) ZeroC, suc qF) ssq0;
                  in oeq_trans OF [oeq_trans OF [cL, m1l], bcr] end;
                val ShiftAbs = Abs("j", natT, mult (binom ZeroC (suc (Bound 0))) (binom nF0 (sub (suc qF) (suc (Bound 0)))));
                val congShift =
                  let
                    val jF = Free("j", natT);
                    val b0Sj = binom0SS2_at jF;
                    val cL = mult_cong_lS2 (binom ZeroC (suc jF), ZeroC, binom nF0 (sub (suc qF) (suc jF))) b0Sj;
                    val m0 = mult0lS2_at (binom nF0 (sub (suc qF) (suc jF)));
                    val body = oeq_trans OF [cL, m0];
                    val dis = Thm.implies_intr (ctermSub (jT (le jF qF))) body;
                    val allm = Thm.forall_intr (ctermSub jF) dis;
                  in sum_cong_at (ShiftAbs, zeroAbs, qF) allm end;
                val sz = sum_zero_at qF;
                val shift0 = oeq_trans OF [congShift, sz];
                val p1 = add_cong_lS2 (Fsq0red, binom nF0 (suc qF), sumf ShiftAbs qF) F0_reduce;
                val p2 = add_cong_rS2 (binom nF0 (suc qF), sumf ShiftAbs qF, ZeroC) shift0;
                val a0r = add0rS2_at (binom nF0 (suc qF));
                val lhsSq = oeq_trans OF [oeq_trans OF [oeq_trans OF [peel, p1], p2], a0r];
                val a0n = add0S2_at nF0;
                val rhsC = binom_cong_l2 (suc qF, add ZeroC nF0, nF0) a0n;
                val rhsCs= oeq_sym OF [rhsC];
                val vbody0Sq = oeq_trans OF [lhsSq, rhsCs];
                val hqsym = oeq_sym OF [hqThm];
                val transported = substPredS2 (predAbs ZeroC, suc qF, kF) hqsym vbody0Sq;
              in transported end;
            val elimd = exE_elimS2 (PabsE, goalC) (Thm.assume (ctermSub hB)) "q" bodyFn;
            val dis = Thm.implies_intr (ctermSub hB) elimd;
          in dis end;

        val bodyK = disjE_elimS2 (oeq kF ZeroC, exTerm, goalC) dz caseA caseB;
        val allMinor = Thm.forall_intr (ctermSub kF) bodyK;
      in allI_S2 (predAbs ZeroC) allMinor end;

    (* ====================================================================
       STEP  m = x -> Suc x.   IH : Forall k. P_x(k).
       ==================================================================== *)
    val xF = Free("x", natT);
    val ihprop = jT (predForall xF);
    val IH = Thm.assume (ctermSub ihprop);
    fun IH_at t = allE_S2 (predAbs xF) t IH;

    val stepconcl =
      let
        val kF = Free("k", natT);
        val dz = dzos_at kF;
        val goalC = vbody (suc xF) kF;

        val caseA =
          let
            val hA = jT (oeq kF ZeroC);
            val sf0 = sumf0_at (vsAbs (suc xF) ZeroC);
            val bsx0= binomN0S2_at (suc xF);
            val cL  = mult_cong_lS2 (binom (suc xF) ZeroC, suc ZeroC, binom nF0 (sub ZeroC ZeroC)) bsx0;
            val m1l = mult1lS2_at (binom nF0 (sub ZeroC ZeroC));
            val s00 = subN0S2_at ZeroC;
            val bcr = binom_cong_r2 (nF0, sub ZeroC ZeroC, ZeroC) s00;
            val bn0 = binomN0S2_at nF0;
            val lhs1 = oeq_trans OF [sf0, cL];
            val lhs2 = oeq_trans OF [lhs1, m1l];
            val lhs3 = oeq_trans OF [lhs2, bcr];
            val lhsZ = oeq_trans OF [lhs3, bn0];
            val rhsZ = binomN0S2_at (add (suc xF) nF0);
            val vbodySx0 = oeq_trans OF [lhsZ, oeq_sym OF [rhsZ]];
            val hAthm = Thm.assume (ctermSub hA);
            val hAsym = oeq_sym OF [hAthm];
            val transported = substPredS2 (predAbs (suc xF), ZeroC, kF) hAsym vbodySx0;
            val dis = Thm.implies_intr (ctermSub hA) transported;
          in dis end;

        val exTerm = mkExSuc kF;
        val caseB =
          let
            val hB = jT exTerm;
            val PabsE = Abs("q", natT, oeq kF (suc (Bound 0)));
            fun bodyFn qF hqThm =
              let
                val axn   = add xF nF0;
                val G1q = vsAbs xF qF;
                val G2  = Abs("j", natT, mult (binom xF (suc (Bound 0))) (binom nF0 (sub qF (Bound 0))));

                val Fsq = vsAbs (suc xF) (suc qF);
                val peel = beta_norm (Drule.infer_instantiate ctxtSub
                      [(("f",0), ctermSub Fsq), (("n",0), ctermSub qF)] sum_peel_first);
                val Fsq0red = mult (binom (suc xF) ZeroC) (binom nF0 (sub (suc qF) ZeroC));
                val ShiftAbs = Abs("j", natT, mult (binom (suc xF) (suc (Bound 0))) (binom nF0 (sub (suc qF) (suc (Bound 0)))));

                val F0_reduce =
                  let
                    val bsx0= binomN0S2_at (suc xF);
                    val cL  = mult_cong_lS2 (binom (suc xF) ZeroC, suc ZeroC, binom nF0 (sub (suc qF) ZeroC)) bsx0;
                    val m1l = mult1lS2_at (binom nF0 (sub (suc qF) ZeroC));
                    val ssq0= subN0S2_at (suc qF);
                    val bcr = binom_cong_r2 (nF0, sub (suc qF) ZeroC, suc qF) ssq0;
                  in oeq_trans OF [oeq_trans OF [cL, m1l], bcr] end;

                val GaddAbs = Abs("j", natT, add (mult (binom xF (Bound 0)) (binom nF0 (sub qF (Bound 0))))
                                                 (mult (binom xF (suc (Bound 0))) (binom nF0 (sub qF (Bound 0)))));
                val congShift =
                  let
                    val jF = Free("j", natT);
                    val ssub = subSSS2_at (qF, jF);
                    val bcr  = binom_cong_r2 (nF0, sub (suc qF) (suc jF), sub qF jF) ssub;
                    val step0 = mult_cong_rS2 (binom (suc xF) (suc jF),
                                  binom nF0 (sub (suc qF) (suc jF)), binom nF0 (sub qF jF)) bcr;
                    val pasc = binomSSS2_at (xF, jF);
                    val MA = binom nF0 (sub qF jF);
                    val step1 = mult_cong_lS2 (binom (suc xF) (suc jF), add (binom xF jF) (binom xF (suc jF)), MA) pasc;
                    val rdst = rdistS2_at (binom xF jF, binom xF (suc jF), MA);
                    val body = oeq_trans OF [oeq_trans OF [step0, step1], rdst];
                    val dis = Thm.implies_intr (ctermSub (jT (le jF qF))) body;
                    val allm = Thm.forall_intr (ctermSub jF) dis;
                  in sum_cong_at (ShiftAbs, GaddAbs, qF) allm end;

                val sadd = beta_norm (Drule.infer_instantiate ctxtSub
                      [(("f",0), ctermSub G1q), (("g",0), ctermSub G2), (("n",0), ctermSub qF)] sum_add);
                val saddS = oeq_sym OF [sadd];
                val shiftSum = oeq_trans OF [congShift, saddS];

                val IHq = IH_at qF;
                val sumG1q = IHq;

                val FxSq = vsAbs xF (suc qF);
                val peelx = beta_norm (Drule.infer_instantiate ctxtSub
                      [(("f",0), ctermSub FxSq), (("n",0), ctermSub qF)] sum_peel_first);
                val FxSq0red = mult (binom xF ZeroC) (binom nF0 (sub (suc qF) ZeroC));
                val XShiftAbs = Abs("j", natT, mult (binom xF (suc (Bound 0))) (binom nF0 (sub (suc qF) (suc (Bound 0)))));
                val Fx0_reduce =
                  let
                    val bx0 = binomN0S2_at xF;
                    val cL  = mult_cong_lS2 (binom xF ZeroC, suc ZeroC, binom nF0 (sub (suc qF) ZeroC)) bx0;
                    val m1l = mult1lS2_at (binom nF0 (sub (suc qF) ZeroC));
                    val ssq0= subN0S2_at (suc qF);
                    val bcr = binom_cong_r2 (nF0, sub (suc qF) ZeroC, suc qF) ssq0;
                  in oeq_trans OF [oeq_trans OF [cL, m1l], bcr] end;
                val congX =
                  let
                    val jF = Free("j", natT);
                    val ssub = subSSS2_at (qF, jF);
                    val bcr  = binom_cong_r2 (nF0, sub (suc qF) (suc jF), sub qF jF) ssub;
                    val body = mult_cong_rS2 (binom xF (suc jF),
                                  binom nF0 (sub (suc qF) (suc jF)), binom nF0 (sub qF jF)) bcr;
                    val dis = Thm.implies_intr (ctermSub (jT (le jF qF))) body;
                    val allm = Thm.forall_intr (ctermSub jF) dis;
                  in sum_cong_at (XShiftAbs, G2, qF) allm end;
                val pe1 = add_cong_lS2 (FxSq0red, binom nF0 (suc qF), sumf XShiftAbs qF) Fx0_reduce;
                val pe2 = add_cong_rS2 (binom nF0 (suc qF), sumf XShiftAbs qF, sumf G2 qF) congX;
                val peelxR = oeq_trans OF [oeq_trans OF [peelx, pe1], pe2];
                val IHsq = IH_at (suc qF);
                val eqB = oeq_trans OF [oeq_sym OF [peelxR], IHsq];

                val l1 = add_cong_lS2 (Fsq0red, binom nF0 (suc qF), sumf ShiftAbs qF) F0_reduce;
                val l2 = add_cong_rS2 (binom nF0 (suc qF), sumf ShiftAbs qF, add (sumf G1q qF) (sumf G2 qF)) shiftSum;
                val l3 = add_cong_rS2 (binom nF0 (suc qF), add (sumf G1q qF) (sumf G2 qF),
                                       add (binom axn qF) (sumf G2 qF))
                                      (add_cong_lS2 (sumf G1q qF, binom axn qF, sumf G2 qF) sumG1q);
                val lhsAll = oeq_trans OF [oeq_trans OF [oeq_trans OF [peel, l1], l2], l3];

                val Bt = binom nF0 (suc qF);
                val At = binom axn qF;
                val Ct = sumf G2 qF;
                val r_as1 = addassocS2_at (Bt, At, Ct);
                val r_as1s= oeq_sym OF [r_as1];
                val r_cm  = addcommS2_at (Bt, At);
                val r_cmc = add_cong_lS2 (add Bt At, add At Bt, Ct) r_cm;
                val r_as2 = addassocS2_at (At, Bt, Ct);
                val reshuffle = oeq_trans OF [oeq_trans OF [r_as1s, r_cmc], r_as2];
                val lhsResh = oeq_trans OF [lhsAll, reshuffle];
                val applyB = add_cong_rS2 (At, add Bt Ct, binom axn (suc qF)) eqB;
                val lhsFold = oeq_trans OF [lhsResh, applyB];

                val aSuc = addSucS2_at (xF, nF0);
                val rhsCong = binom_cong_l2 (suc qF, add (suc xF) nF0, suc axn) aSuc;
                val pascR = binomSSS2_at (axn, qF);
                val rhsAll = oeq_trans OF [rhsCong, pascR];
                val vbodySxSq = oeq_trans OF [lhsFold, oeq_sym OF [rhsAll]];

                val hqsym = oeq_sym OF [hqThm];
                val transported = substPredS2 (predAbs (suc xF), suc qF, kF) hqsym vbodySxSq;
              in transported end;
            val elimd = exE_elimS2 (PabsE, goalC) (Thm.assume (ctermSub hB)) "q" bodyFn;
            val dis = Thm.implies_intr (ctermSub hB) elimd;
          in dis end;

        val bodyK = disjE_elimS2 (oeq kF ZeroC, exTerm, goalC) dz caseA caseB;
        val allMinor = Thm.forall_intr (ctermSub kF) bodyK;
      in allI_S2 (predAbs (suc xF)) allMinor end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val () = out "VAND_BUILD_OK\n";

(* ---- intended statement (m,n,k all general) + soundness probe ---- *)
val mVs = Var (("m",0), natT);
val nVsv = Var (("n",0), natT);   (* varify generalised n too *)
val i_vandermonde =
  let
    val kF = Free("k", natT);
    fun summAbs kt = Abs("j", natT, mult (binom mVs (Bound 0)) (binom nVsv (sub kt (Bound 0))));
    val body = Term.lambda kF (oeq (sumf (summAbs kF) kF) (binom (add mVs nVsv) kF));
  in jT (mkForall body) end;
val r_vandermonde = checkSub ("vandermonde", vandermonde, i_vandermonde);

val s_vand_nontrivial =
  let
    val kF = Free("k", natT);
    fun badAbs kt = Abs("j", natT, mult (binom mVs (Bound 0)) (binom nVsv kt));
    val badBody = Term.lambda kF (oeq (sumf (badAbs kF) kF) (binom (add mVs nVsv) kF));
  in not ((Thm.prop_of vandermonde) aconv (jT (mkForall badBody))) end;

val () =
  if r_vandermonde andalso s_vand_nontrivial
  then out "OK vandermonde\n"
  else out "FAIL vandermonde\n";

val () =
  if r_vandermonde andalso s_vand_nontrivial andalso r_sum_zero
  then out "VANDERMONDE_OK\n"
  else out "VANDERMONDE_FAIL\n";
