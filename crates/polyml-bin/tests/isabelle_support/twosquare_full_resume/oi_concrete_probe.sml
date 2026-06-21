
(* ============================================================================
   VERIFIER SOUNDNESS PROBE — concrete sum-of-two-squares decisions by the
   kernel.  EVERYTHING certified on ctxtO / thyO (the topmost foundation theory
   carrying add, mult, Suc, Zero, oeq, oeq_subst, exI, oFalse, Suc_inj,
   Suc_neq_Zero).  Genuine inference only; NO axiom about sums of two squares.

   ACCEPT 5,9,2,13  : prove a witnessed  Ex P Q. oeq (add (P*P)(Q*Q)) n .
   REJECT 3,7,21    : for EVERY candidate (a,b) with a^2,b^2 <= n, prove
                      oeq (add (a*a)(b*b)) n ==> oFalse, so NO witness exists.
   ============================================================================ *)
val () = out "PROBE2_BEGIN\n";

fun mkNum 0 = ZeroC | mkNum k = suc (mkNum (k-1));
val oeq_subst_vO = varify oeq_subst;

(* ground instantiators, all on ctxtO *)
fun add0O   t        = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO t)] add_0_vO);
fun addSucO (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtO [(("m",0), ctermO mt),(("n",0), ctermO nt)] add_Suc_vO);
fun mult0O  t        = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO t)] mult_0_v);
fun multSucO (mt,nt) = beta_norm (Drule.infer_instantiate ctxtO [(("m",0), ctermO mt),(("n",0), ctermO nt)] mult_Suc_v);
fun reflO   t        = beta_norm (Drule.infer_instantiate ctxtO [(("a",0), ctermO t)] oeq_refl_vO);

(* congruence helpers on ctxtO via oeq_subst *)
fun sucCongO hpq (aT,bT) =
  let val Pabs = Abs("z", natT, oeq (suc aT) (suc (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtO
            [(("P",0), ctermO Pabs), (("a",0), ctermO aT), (("b",0), ctermO bT)] oeq_subst_vO)
  in (inst OF [hpq]) OF [reflO (suc aT)] end;
fun addCongLO (aT,bT,kT) hpq =     (* hpq: oeq aT bT  ->  oeq (add aT kT)(add bT kT) *)
  let val Pabs = Abs("z", natT, oeq (add aT kT) (add (Bound 0) kT))
      val inst = beta_norm (Drule.infer_instantiate ctxtO
            [(("P",0), ctermO Pabs), (("a",0), ctermO aT), (("b",0), ctermO bT)] oeq_subst_vO)
  in (inst OF [hpq]) OF [reflO (add aT kT)] end;
fun addCongRO (hT,aT,bT) hpq =     (* hpq: oeq aT bT  ->  oeq (add hT aT)(add hT bT) *)
  let val Pabs = Abs("z", natT, oeq (add hT aT) (add hT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtO
            [(("P",0), ctermO Pabs), (("a",0), ctermO aT), (("b",0), ctermO bT)] oeq_subst_vO)
  in (inst OF [hpq]) OF [reflO (add hT aT)] end;
(* oeq transitivity/symmetry on ctxtO via oeq_subst *)
fun transO h1 h2 (aT,bT,cT) =      (* h1: oeq aT bT, h2: oeq bT cT -> oeq aT cT *)
  let val Pabs = Abs("z", natT, oeq aT (Bound 0))
      val inst = beta_norm (Drule.infer_instantiate ctxtO
            [(("P",0), ctermO Pabs), (("a",0), ctermO bT), (("b",0), ctermO cT)] oeq_subst_vO)
  in (inst OF [h2]) OF [h1] end;
fun symO h (aT,bT) =               (* h: oeq aT bT -> oeq bT aT *)
  let val Pabs = Abs("z", natT, oeq (Bound 0) aT)
      val inst = beta_norm (Drule.infer_instantiate ctxtO
            [(("P",0), ctermO Pabs), (("a",0), ctermO aT), (("b",0), ctermO bT)] oeq_subst_vO)
  in (inst OF [h]) OF [reflO aT] end;

(* evalAdd a b : |- oeq (add (mkNum a)(mkNum b)) (mkNum (a+b)) *)
fun evalAdd a b =
  if a = 0 then add0O (mkNum b)
  else
    let val prev = evalAdd (a-1) b                              (* oeq (add (a-1) b) (a-1+b) *)
        val step = addSucO (mkNum (a-1), mkNum b)               (* oeq (add (Suc(a-1)) b)(Suc (add (a-1) b)) *)
        val sc   = sucCongO prev (add (mkNum (a-1)) (mkNum b), mkNum ((a-1)+b))
                   (* oeq (Suc (add (a-1) b))(Suc (a-1+b)) = (Suc(add(a-1)b))(mkNum(a+b)) *)
    in transO step sc (add (suc (mkNum (a-1))) (mkNum b), suc (add (mkNum (a-1)) (mkNum b)), mkNum (a+b)) end;

(* evalMult a b : |- oeq (mult (mkNum a)(mkNum b)) (mkNum (a*b)) ; mult_Suc: mult(Suc m)n = add n (mult m n) *)
fun evalMult a b =
  if a = 0 then mult0O (mkNum b)
  else
    let val prevM = evalMult (a-1) b                            (* oeq (mult (a-1) b)((a-1)*b) *)
        val step  = multSucO (mkNum (a-1), mkNum b)             (* oeq (mult (Suc(a-1)) b)(add b (mult (a-1) b)) *)
        val congR = addCongRO (mkNum b, mult (mkNum (a-1)) (mkNum b), mkNum ((a-1)*b)) prevM
                    (* oeq (add b (mult (a-1) b))(add b ((a-1)*b)) *)
        val evA   = evalAdd b ((a-1)*b)                         (* oeq (add b ((a-1)*b))(b+(a-1)*b) *)
        val t1    = transO congR evA (add (mkNum b) (mult (mkNum (a-1)) (mkNum b)),
                                      add (mkNum b) (mkNum ((a-1)*b)), mkNum (a*b))
    in transO step t1 (mult (suc (mkNum (a-1))) (mkNum b),
                       add (mkNum b) (mult (mkNum (a-1)) (mkNum b)), mkNum (a*b)) end;

(* evalSumSq a b : |- oeq (add (mult a a)(mult b b)) (mkNum (a*a+b*b)) *)
fun evalSumSq a b =
  let val ma = evalMult a a
      val mb = evalMult b b
      val cL = addCongLO (mult (mkNum a)(mkNum a), mkNum (a*a), mult (mkNum b)(mkNum b)) ma
               (* oeq (add (a*a)(b*b))(add (mkNum(a*a))(b*b)) *)
      val cR = addCongRO (mkNum (a*a), mult (mkNum b)(mkNum b), mkNum (b*b)) mb
               (* oeq (add (mkNum(a*a))(b*b))(add (mkNum(a*a))(mkNum(b*b))) *)
      val sE = evalAdd (a*a) (b*b)
               (* oeq (add (a*a)(b*b))(a*a+b*b) *)
      val t1 = transO cR sE (add (mkNum (a*a)) (mult (mkNum b)(mkNum b)),
                             add (mkNum (a*a)) (mkNum (b*b)), mkNum (a*a+b*b))
  in transO cL t1 (add (mult (mkNum a)(mkNum a)) (mult (mkNum b)(mkNum b)),
                   add (mkNum (a*a)) (mult (mkNum b)(mkNum b)), mkNum (a*a+b*b)) end;

(* numEqFalse m n (m<>n) : |- oeq (mkNum m)(mkNum n) ==> oFalse *)
fun numEqFalse m n =
  let val hypT = jT (oeq (mkNum m) (mkNum n))
      val hyp  = Thm.assume (ctermO hypT)
      val body =
        if m = 0 then
          let val sym = symO hyp (mkNum 0, mkNum n)                  (* oeq (Suc..) 0 *)
              val snz = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO (mkNum (n-1)))] Suc_neq_Zero_v)
          in snz OF [sym] end
        else if n = 0 then
          let val snz = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO (mkNum (m-1)))] Suc_neq_Zero_v)
          in snz OF [hyp] end
        else
          let val inj = beta_norm (Drule.infer_instantiate ctxtO
                          [(("a",0), ctermO (mkNum (m-1))),(("b",0), ctermO (mkNum (n-1)))] Suc_inj_v)
              val peeled = inj OF [hyp]                              (* oeq m' n' *)
          in (numEqFalse (m-1) (n-1)) OF [peeled] end
  in Thm.implies_intr (ctermO hypT) body end;

val () = out "PROBE2_HELPERS_OK\n";

(* ACCEPT *)
fun acceptTwoSq n (a,b) =
  let
    val _    = if (a*a+b*b) = n then () else raise Fail ("bad witness for "^Int.toString n)
    val sumE = evalSumSq a b                                       (* oeq (add (a*a)(b*b)) (mkNum n) *)
    val innerPred = Abs("Q", natT, oeq (add (mult (mkNum a)(mkNum a)) (mult (Bound 0)(Bound 0))) (mkNum n))
    val exiInner  = beta_norm (Drule.infer_instantiate ctxtO
                      [(("P",0), ctermO innerPred), (("a",0), ctermO (mkNum b))] exI_v)
    val innerThm  = exiInner OF [sumE]
    val outerPred = Abs("P", natT, mkEx (Abs("Q", natT,
                       oeq (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))) (mkNum n))))
    val exiOuter  = beta_norm (Drule.infer_instantiate ctxtO
                      [(("P",0), ctermO outerPred), (("a",0), ctermO (mkNum a))] exI_v)
    val fullThm   = exiOuter OF [innerThm]
    val nhyp      = length (Thm.hyps_of fullThm)
  in out ("ACCEPT n=" ^ Int.toString n ^ " witness=(" ^ Int.toString a ^ "," ^ Int.toString b
          ^ ") Ex P Q. P^2+Q^2=n proved, hyps=" ^ Int.toString nhyp ^ "\n") end;

val () = acceptTwoSq 2  (1,1);
val () = acceptTwoSq 5  (1,2);
val () = acceptTwoSq 9  (3,0);
val () = acceptTwoSq 13 (2,3);

(* REJECT *)
fun isqrt n = let fun go k = if k*k > n then k-1 else go (k+1) in go 0 end;
fun rejectTwoSq n =
  let
    val s = isqrt n
    val cands = List.concat (List.tabulate (s+1, fn a => List.tabulate (s+1, fn b => (a,b))))
    val results = List.map (fn (a,b) =>
        let val v = a*a + b*b in
          if v = n then (out ("REJECT_FAIL n=" ^ Int.toString n ^ " witness ("^Int.toString a^","^Int.toString b^")!\n"); false)
          else
            let val sumE = evalSumSq a b                            (* oeq (add (a*a)(b*b)) (mkNum v) *)
                val lhsT = add (mult (mkNum a)(mkNum a)) (mult (mkNum b)(mkNum b))
                val hyp  = Thm.assume (ctermO (jT (oeq lhsT (mkNum n))))
                val vEqN = transO (symO sumE (lhsT, mkNum v)) hyp (mkNum v, lhsT, mkNum n)  (* oeq v n *)
                val fls  = (numEqFalse v n) OF [vEqN]
                val impl = Thm.implies_intr (ctermO (jT (oeq lhsT (mkNum n)))) fls
            in length (Thm.hyps_of impl) = 0 end
        end) cands
  in out ("REJECT n=" ^ Int.toString n ^ " candidates=" ^ Int.toString (length cands)
          ^ " all_refuted=" ^ Bool.toString (List.all (fn x=>x) results) ^ "\n") end;

val () = rejectTwoSq 3;
val () = rejectTwoSq 7;
val () = rejectTwoSq 21;

val () = out "PROBE2_END\n";
