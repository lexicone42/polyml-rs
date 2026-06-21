(* ============================================================================
   GENUINE COMPUTATION of sigma at concrete points by kernel inference.
   ============================================================================ *)
val () = out "VF_SIGMA_COMPUTE_BEGIN\n";

fun numC 0 = ZeroC | numC n = suc (numC (n-1));

fun addEval (a, b) =
  if a = 0 then add0Sg_at (numC b)
  else
    let val aS = addSuc_Sg (numC (a-1), numC b)
        val rec0 = addEval (a-1, b)
    in oeq_trans OF [aS, Suc_cong OF [rec0]] end;

fun multEval (d, k) =
  if d = 0 then beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig (numC k))] mult_0_vSg)
  else
    let val mS = multSucSg_at (numC (d-1), numC k)
        val recm = multEval (d-1, k)
        val cong = add_cong_rSg (numC k, mult (numC (d-1)) (numC k), numC ((d-1)*k)) recm
        val ae = addEval (k, (d-1)*k)
    in oeq_trans OF [oeq_trans OF [mS, cong], ae] end;

fun dvd_concrete (d, n, w) =
  let val me = multEval (d, w) in dvd_introSg (numC d, numC n, numC w) (oeq_sym OF [me]) end;

fun neq_num (a, b) =
  let val heq = Thm.assume (ctermSig (jT (oeq (numC a)(numC b))))
      fun derive (a, b, heq) =
        if a = 0 then (Suc_neq_Zero_Sg (numC (b-1))) OF [oeq_sym OF [heq]]
        else if b = 0 then (Suc_neq_Zero_Sg (numC (a-1))) OF [heq]
        else derive (a-1, b-1, (Suc_inj_Sg (numC (a-1), numC (b-1))) OF [heq])
      val fls = derive (a, b, heq)
  in impI_Sg (oeq (numC a)(numC b), oFalseC) (Thm.implies_intr (ctermSig (jT (oeq (numC a)(numC b)))) fls) end;

val mult_Suc_right_vSg = varify mult_Suc_right;
fun multSrSg (nt, mt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("n",0), ctermSig nt),(("m",0), ctermSig mt)] mult_Suc_right_vSg);
val add_left_cancel_vSg = varify add_left_cancel;
fun addLCancelSg (mt, at, bt) hyp = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("a",0), ctermSig at),(("b",0), ctermSig bt)] add_left_cancel_vSg) OF [hyp];

val () = out "VF_EXTRA_LEMMAS_OK\n";

(* refute_lt (n, M, Z, heq) : n < M, heq : oeq (numC n) (add (numC M) Z), Z abstract.
   Requires M - n - 1 >= 1.  Peels n+1 Suc_inj, residual Suc-headed -> Suc_neq_Zero. *)
fun refute_lt (n, M, Z, heq) =
  let
    fun peel (i, accThm) =
      if i = n then accThm
      else
        let val aS = addSuc_Sg (numC (M - i - 1), Z)            (* add (Suc(M-i-1)) Z = Suc(add (M-i-1) Z) *)
            val rhsStep = oeq_trans OF [accThm, aS]             (* oeq (numC(n-i)) (Suc(add (M-i-1) Z)) *)
            val inj = (Suc_inj_Sg (numC (n-i-1), add (numC (M-i-1)) Z)) OF [rhsStep]
        in peel (i+1, inj) end
    val final = peel (0, heq)                                   (* oeq (numC 0) (add (numC (M-n)) Z) *)
    val rem = M - n
    val _ = if rem < 1 then raise Fail "refute_lt rem<1" else ()
    val aS = addSuc_Sg (numC (rem-1), Z)                        (* add (Suc(rem-1)) Z = Suc(add (rem-1) Z) *)
    val step = oeq_trans OF [final, aS]                         (* oeq 0 (Suc(add (rem-1) Z)) *)
  in (Suc_neq_Zero_Sg (add (numC (rem-1)) Z)) OF [oeq_sym OF [step]] end;

(* refute_witness (lvl, d, n, kterm, heq) : d>=1, n>=1, d does NOT divide n.
   heq : oeq (numC n) (mult (numC d) kterm).  Produces oFalse.
   lvl makes all introduced witness Free names unique per recursion level. *)
fun refute_witness (lvl, d, n, kterm, heq) =
  let
    val sfx = "_L" ^ Int.toString lvl
    val dz = dzosSg_at kterm
    val PsZ = Term.lambda (Free("kq"^sfx,natT)) (oeq kterm (suc (Free("kq"^sfx,natT))))   (* %q. oeq k (Suc q) *)
    val caseZ =
      let val hk0 = Thm.assume (ctermSig (jT (oeq kterm ZeroC)))
          val Pabs = Term.lambda (Free("zc",natT)) (oeq (numC n) (mult (numC d) (Free("zc",natT))))
          val heq0 = substPredSg (Pabs, kterm, ZeroC) hk0 heq                     (* oeq n (mult d 0) *)
          val neq0 = oeq_trans OF [heq0, multEval (d, 0)]                          (* oeq n 0 *)
          val fls  = (Suc_neq_Zero_Sg (numC (n-1))) OF [neq0]
      in Thm.implies_intr (ctermSig (jT (oeq kterm ZeroC))) fls end
    val caseS =
      let
        fun body qv hkq =
          let val Pabs = Term.lambda (Free("zc2",natT)) (oeq (numC n) (mult (numC d) (Free("zc2",natT))))
              val heqS = substPredSg (Pabs, kterm, suc qv) hkq heq               (* oeq n (mult d (Suc q)) *)
              val heqA = oeq_trans OF [heqS, multSrSg (numC d, qv)]               (* oeq n (add d (mult d q)) *)
          in
            if n >= d then
              let val ae = addEval (d, n-d)                                        (* oeq (add d (n-d)) n *)
                  val combo = oeq_trans OF [ae, heqA]                              (* oeq (add d (n-d)) (add d (mult d q)) *)
                  val canc = addLCancelSg (numC d, numC (n-d), mult (numC d) qv) combo  (* oeq (n-d) (mult d q) *)
              in refute_witness (lvl+1, d, n-d, qv, canc) end
            else
              let
                val dzq = dzosSg_at qv
                val PrZ = Term.lambda (Free("rq"^sfx,natT)) (oeq qv (suc (Free("rq"^sfx,natT))))
                val cqZ =
                  let val hq0 = Thm.assume (ctermSig (jT (oeq qv ZeroC)))
                      val Pq = Term.lambda (Free("zq",natT)) (oeq (numC n) (add (numC d) (mult (numC d) (Free("zq",natT)))))
                      val h0 = substPredSg (Pq, qv, ZeroC) hq0 heqA               (* oeq n (add d (mult d 0)) *)
                      val cong = add_cong_rSg (numC d, mult (numC d) ZeroC, ZeroC) (multEval (d,0))
                      val h0d = oeq_trans OF [h0, cong]                           (* oeq n (add d 0) *)
                      val hnd = oeq_trans OF [h0d, add0rSg_at (numC d)]           (* oeq n d *)
                      val fls = mp_Sg (oeq (numC n) (numC d), oFalseC) (neq_num (n, d)) hnd
                  in Thm.implies_intr (ctermSig (jT (oeq qv ZeroC))) fls end
                val cqS =
                  let
                      fun bodyR rv hqr =
                        let val Pr = Term.lambda (Free("zr",natT)) (oeq (numC n) (add (numC d) (mult (numC d) (Free("zr",natT)))))
                            val hSr = substPredSg (Pr, qv, suc rv) hqr heqA       (* oeq n (add d (mult d (Suc r))) *)
                            val cong2 = add_cong_rSg (numC d, mult (numC d) (suc rv), add (numC d) (mult (numC d) rv)) (multSrSg (numC d, rv))
                            val h2 = oeq_trans OF [hSr, cong2]                    (* oeq n (add d (add d (mult d r))) *)
                            val aassoc = addassocSg_at (numC d, numC d, mult (numC d) rv)  (* oeq (add (add d d) Z) (add d (add d Z)) *)
                            val dd = addEval (d, d)                              (* oeq (add d d) (2d) *)
                            val ddcong = add_cong_lSg (add (numC d) (numC d), numC (2*d), mult (numC d) rv) dd (* oeq (add (add d d) Z) (add (2d) Z) *)
                            (* (add (2d) Z) = (add (add d d) Z) [sym ddcong] = (add d (add d Z)) [aassoc] = n [sym h2] *)
                            val twoZ_n = oeq_trans OF [oeq_trans OF [oeq_sym OF [ddcong], aassoc], oeq_sym OF [h2]]
                            val h2d = oeq_sym OF [twoZ_n]                         (* oeq n (add (2d) (mult d r)) *)
                        in refute_lt (n, 2*d, mult (numC d) rv, h2d) end
                      val fls = exE_elimSg (PrZ, oFalseC) (Thm.assume (ctermSig (jT (mkEx PrZ)))) ("r_in"^sfx) bodyR
                  in Thm.implies_intr (ctermSig (jT (mkEx PrZ))) fls end
              in disjE_elimSg (oeq qv ZeroC, mkEx PrZ, oFalseC) dzq cqZ cqS end
          end
        val fls = exE_elimSg (PsZ, oFalseC) (Thm.assume (ctermSig (jT (mkEx PsZ)))) ("q_in"^sfx) body
      in Thm.implies_intr (ctermSig (jT (mkEx PsZ))) fls end
  in disjE_elimSg (oeq kterm ZeroC, mkEx PsZ, oFalseC) dz caseZ caseS end;

(* ndvd_concrete (d, n) : jT (neg (dvd (numC d) (numC n)))  [d does NOT divide n, d>=1,n>=1] *)
fun ndvd_concrete (d, n) =
  let
    val hdvd = Thm.assume (ctermSig (jT (dvd (numC d) (numC n))))   (* Ex k. oeq n (mult d k) *)
    val Pk = Term.lambda (Free("kk",natT)) (oeq (numC n) (mult (numC d) (Free("kk",natT))))
    fun body kv hk = refute_witness (0, d, n, kv, hk)
    val fls = exE_elimSg (Pk, oFalseC) hdvd "k_w" body
  in impI_Sg (dvd (numC d)(numC n), oFalseC) (Thm.implies_intr (ctermSig (jT (dvd (numC d)(numC n)))) fls) end;

val () = out "VF_NDVD_OK\n";

(* ============================================================================
   sigma_eval n : jT (oeq (sigma (numC n)) (numC (sum-of-divisors n)))
   by unfolding sigma_def -> sumf -> swt at each index 0..n, deciding dvd.
   ============================================================================ *)
val () = out "VF_SIGMA_EVAL_BEGIN\n";

(* swt evaluation at concrete (n, d) : oeq (swt (numC n) (numC d)) (numC (if d|n then d else 0)) *)
fun swt_eval (n, d) =
  if (d > 0 andalso n mod d = 0) then
    (* d | n : swt n d = d  ; need jT (dvd d n) via witness n/d *)
    let val hdvd = dvd_concrete (d, n, n div d)            (* jT (dvd d n) *)
    in swt_eval_dvd (numC n, numC d) hdvd end             (* oeq (swt n d) d *)
  else
    (* d does not divide n (incl. d=0 since 0 does not divide n>0) : swt n d = 0 *)
    let val hndvd =
          if d = 0 then ndvd_zero_Sg (numC (n-1))         (* neg(dvd 0 (Suc(n-1))) = neg(dvd 0 n) *)
          else ndvd_concrete (d, n)                        (* neg(dvd d n) *)
    in swt_eval_ndvd (numC n, numC d) hndvd end;          (* oeq (swt n d) 0 *)

(* sumf (swt (numC n)) (numC m) evaluated to numeral, m <= n.
   returns (value, thm : oeq (sumf (swt (numC n)) (numC m)) (numC value)) *)
fun sumf_swt_eval (n, m) =
  let val swtnAbs = swtC $ (numC n)                       (* swt n : nat=>nat (partial app) *)
  in
    if m = 0 then
      let val s0 = sumf0Sg_at swtnAbs                     (* sumf (swt n) 0 = (swt n) 0 = swt n 0 [beta] *)
          val se = swt_eval (n, 0)                        (* swt n 0 = numC 0 (0 does not divide n>0) *)
      in (0, oeq_trans OF [s0, se]) end                   (* oeq (sumf (swt n) 0) 0 *)
    else
      let
        val (vprev, tprev) = sumf_swt_eval (n, m-1)       (* oeq (sumf (swt n)(m-1)) (numC vprev) *)
        val sS = sumfSucSg_at (swtnAbs, numC (m-1))       (* sumf (swt n) m = add (sumf (swt n)(m-1)) ((swt n) m) [beta: swt n m] *)
        val vm = (if (m > 0 andalso n mod m = 0) then m else 0)
        val seM = swt_eval (n, m)                         (* swt n m = numC vm *)
        (* add (sumf (swt n)(m-1)) (swt n m) = add (numC vprev) (numC vm) [cong both] = numC(vprev+vm) *)
        val cL = add_cong_lSg (sumf swtnAbs (numC (m-1)), numC vprev, swt (numC n) (numC m)) tprev
                 (* oeq (add (sumf..) (swt n m)) (add (numC vprev) (swt n m)) *)
        val cR = add_cong_rSg (numC vprev, swt (numC n) (numC m), numC vm) seM
                 (* oeq (add (numC vprev) (swt n m)) (add (numC vprev) (numC vm)) *)
        val ae = addEval (vprev, vm)                      (* oeq (add (numC vprev)(numC vm)) (numC(vprev+vm)) *)
        val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [sS, cL], cR], ae]
                 (* oeq (sumf (swt n) m) (numC (vprev+vm)) *)
      in (vprev+vm, chain) end
  end;

(* sigma_eval n : oeq (sigma (numC n)) (numC sigma_value) *)
fun sigma_eval n =
  let
    val sdef = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig (numC n))] (varify sigma_def_ax))
               (* oeq (sigma n) (sumf (swt n) n) *)
    val (v, tsum) = sumf_swt_eval (n, n)                  (* oeq (sumf (swt n) n) (numC v) *)
    val chain = oeq_trans OF [sdef, tsum]                 (* oeq (sigma n) (numC v) *)
  in (v, chain) end;

val () = out "VF_SIGMA_EVAL_DEFINED\n";
(* ============================================================================
   DECISIVE SOUNDNESS PROBES (genuine computation by kernel inference):
     sigma 6  = 12  (= 2*6)   -> 6  is PERFECT
     sigma 28 = 56  (= 2*28)  -> 28 is PERFECT
     sigma 8  = 15  (<> 16)   -> 8  is NOT perfect
   ============================================================================ *)
val () = out "VF_PROBES_BEGIN\n";

fun report_sigma n =
  let
    val (v, th) = sigma_eval n
    (* check the theorem is exactly oeq (sigma (numC n)) (numC v), 0-hyp *)
    val intended = jT (oeq (sigma (numC n)) (numC v))
    val ac = (Thm.prop_of th) aconv intended
    val nh = length (Thm.hyps_of th)
  in
    out ("SIGMA " ^ Int.toString n ^ " = " ^ Int.toString v
         ^ "  (aconv=" ^ Bool.toString ac ^ ", hyps=" ^ Int.toString nh ^ ")\n");
    (v, th, ac, nh = 0)
  end;

(* sigma 6 = 12 *)
val (v6, th6, ac6, h6) = report_sigma 6;
val () = if v6 = 12 andalso ac6 andalso h6 then out "PROBE_OK sigma 6 = 12 (perfect: 2*6)\n"
         else out ("PROBE_FAIL sigma 6 (v=" ^ Int.toString v6 ^ ")\n");

(* sigma 28 = 56 *)
val (v28, th28, ac28, h28) = report_sigma 28;
val () = if v28 = 56 andalso ac28 andalso h28 then out "PROBE_OK sigma 28 = 56 (perfect: 2*28)\n"
         else out ("PROBE_FAIL sigma 28 (v=" ^ Int.toString v28 ^ ")\n");

(* sigma 8 = 15 <> 16 *)
val (v8, th8, ac8, h8) = report_sigma 8;
val () = if v8 = 15 andalso ac8 andalso h8 then out "PROBE_OK sigma 8 = 15 (NOT perfect: 2*8 = 16 <> 15)\n"
         else out ("PROBE_FAIL sigma 8 (v=" ^ Int.toString v8 ^ ")\n");

(* Confirm perfect/not-perfect via the kernel: build oeq (numC v) (numC (2*n)) and check.
   For 6,28: v = 2*n (perfect).  For 8: v <> 2*n (refute by neq_num). *)
val perfect6 = (v6 = 2*6);
val perfect28 = (v28 = 2*28);
val () = if perfect6 then out "VERDICT 6 PERFECT (sigma 6 = 12 = 2*6)\n" else out "VERDICT 6 NOT-PERFECT?!\n";
val () = if perfect28 then out "VERDICT 28 PERFECT (sigma 28 = 56 = 2*28)\n" else out "VERDICT 28 NOT-PERFECT?!\n";
(* 8 not perfect : prove neg(oeq 15 16) by kernel, demonstrating sigma 8 <> 2*8 *)
val neq_15_16 = neq_num (15, 16);   (* jT (neg (oeq 15 16)) *)
val () = if v8 <> 2*8 then out "VERDICT 8 NOT-PERFECT (sigma 8 = 15 <> 16 = 2*8; neg(oeq 15 16) kernel-proved)\n"
         else out "VERDICT 8 PERFECT?!\n";

val () = out "VF_PROBES_DONE\n";
