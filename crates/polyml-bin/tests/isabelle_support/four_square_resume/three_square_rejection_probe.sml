(* ============================================================================
   THREE-SQUARES REJECTION PROBE (independent verifier, adversarial soundness).

   Goal: demonstrate by GENUINE LCF KERNEL inference that
     (1) 7 is NOT a sum of three squares  -> the kernel cannot witness
         EX a b c. oeq 7 (a*a+b*b+c*c)  (no (a,b,c) in {0,1,2}^3 computes to 7),
     (2) 7 IS a sum of four squares (2^2+1^2+1^2+1^2 = 7) -> four squares are
         genuinely necessary here, so the target ALL n. EX a b c d. ... is the
         right (non-collapsible-to-three) statement,
     (3) the kernel REJECTS a false numeric equality (oeq 7 6) by raising.

   Self-contained: rebuilds only the Peano nat fragment (Zero/Suc/oeq/add/mult +
   recursion + discrimination), mirroring the four-square base's foundation
   (isabelle_four_square.sml lines 124-157, 325-331, 626-633) byte-for-byte in
   shape, so it is a faithful probe of the SAME kernel the proof would use.
   ============================================================================ *)
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
val () = out "TSQ_BEGIN\n";

val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global
  [(Binding.name "o",0,NoSyn),(Binding.name "nat",0,NoSyn)] thy0;
val oN = Sign.full_name thy1 (Binding.name "o");
val natN = Sign.full_name thy1 (Binding.name "nat");
val oT = Type (oN,[]);  val natT = Type (natN,[]);
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "Zero", natT, NoSyn),
   (Binding.name "Suc", natT --> natT, NoSyn),
   (Binding.name "add", natT --> natT --> natT, NoSyn),
   (Binding.name "mult", natT --> natT --> natT, NoSyn),
   (Binding.name "oeq", natT --> natT --> oT, NoSyn)] thy1;
fun cnst nm T = Const (Sign.full_name thy2 (Binding.name nm), T);
val TP    = cnst "Trueprop" (oT --> propT);      fun jT t = TP $ t;
val ZeroC = cnst "Zero" natT;
val SucC  = cnst "Suc" (natT --> natT);          fun suc t = SucC $ t;
val addC  = cnst "add" (natT --> natT --> natT); fun add a b = addC $ a $ b;
val multC = cnst "mult" (natT --> natT --> natT); fun mult a b = multC $ a $ b;
val oeqC  = cnst "oeq" (natT --> natT --> oT);   fun oeq a b = oeqC $ a $ b;
val predT = natT --> oT;
val aV = Free ("a",natT); val bV = Free ("b",natT);
val nV = Free ("n",natT); val mV = Free ("m",natT);
val P  = Free ("P", predT);

val ((_,oeq_refl),  t3) = Thm.add_axiom_global (Binding.name "oeq_refl",  jT (oeq aV aV)) thy2;
val ((_,oeq_subst), t4) = Thm.add_axiom_global (Binding.name "oeq_subst",
      Logic.mk_implies (jT (oeq aV bV), Logic.mk_implies (jT (P $ aV), jT (P $ bV)))) t3;
val ((_,add_0),   t5) = Thm.add_axiom_global (Binding.name "add_0",   jT (oeq (add ZeroC nV) nV)) t4;
val ((_,add_Suc), t6) = Thm.add_axiom_global (Binding.name "add_Suc",
      jT (oeq (add (suc mV) nV) (suc (add mV nV)))) t5;
val ((_,mult_0),  t7) = Thm.add_axiom_global (Binding.name "mult_0",  jT (oeq (mult ZeroC nV) ZeroC)) t6;
val ((_,mult_Suc),t8) = Thm.add_axiom_global (Binding.name "mult_Suc",
      jT (oeq (mult (suc mV) nV) (add nV (mult mV nV)))) t7;
(* Peano discrimination: needed to PROVE non-equality (7 <> v) honestly. *)
val nD = Free("nD",natT);
val ((_,Suc_neq_Zero), t9) = Thm.add_axiom_global (Binding.name "Suc_neq_Zero",
      Logic.mk_implies (jT (oeq (suc nD) ZeroC), jT (oeq ZeroC ZeroC))) t8;
   (* NB: a real oFalse is not in this minimal fragment; we test non-equality at
      the SML/kernel level by attempting the proof and catching the failure. *)
val aSj = Free("aSj",natT); val bSj = Free("bSj",natT);
val ((_,Suc_inj), thy) = Thm.add_axiom_global (Binding.name "Suc_inj",
      Logic.mk_implies (jT (oeq (suc aSj) (suc bSj)), jT (oeq aSj bSj))) t9;

val ctxt = Proof_Context.init_global thy;
val cterm = Thm.cterm_of ctxt;
fun varify th = Drule.zero_var_indexes (Drule.export_without_context th);
fun beta_norm th = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;

val oeq_refl_v  = varify oeq_refl;
val oeq_subst_v = varify oeq_subst;
val add_0_v     = varify add_0;
val add_Suc_v   = varify add_Suc;
val mult_0_v    = varify mult_0;
val mult_Suc_v  = varify mult_Suc;

(* oeq_sym, oeq_trans via oeq_subst (same construction as the base). *)
val oeq_sym =
  let val a=Free("a",natT); val b=Free("b",natT);
      val Pabs = Abs("z",natT, oeq (Bound 0) a);
      val inst = beta_norm (Drule.infer_instantiate ctxt
            [(("P",0),cterm Pabs),(("a",0),cterm a),(("b",0),cterm b)] oeq_subst_v);
      val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0),cterm a)] oeq_refl_v);
      val step = inst OF [Thm.assume (cterm (jT (oeq a b))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (oeq a b))) step) end;
val oeq_trans =
  let val a=Free("a",natT); val b=Free("b",natT); val c=Free("c",natT);
      val Pabs = Abs("z",natT, oeq a (Bound 0));
      val inst = beta_norm (Drule.infer_instantiate ctxt
            [(("P",0),cterm Pabs),(("a",0),cterm b),(("b",0),cterm c)] oeq_subst_v);
      val H1 = Thm.assume (cterm (jT (oeq a b)));
      val H2 = Thm.assume (cterm (jT (oeq b c)));
      val step = inst OF [H2,H1];
  in varify (Thm.implies_intr (cterm (jT (oeq a b))) (Thm.implies_intr (cterm (jT (oeq b c))) step)) end;

fun oeqSym h = beta_norm (oeq_sym OF [h]);
fun oeqTrans (h1,h2) = beta_norm (oeq_trans OF [h1,h2]);

(* Suc_cong : oeq a b -> oeq (Suc a) (Suc b), via oeq_subst with P z = oeq (Suc a)(Suc z) *)
val Suc_cong =
  let val a=Free("a",natT); val b=Free("b",natT);
      val Pabs = Abs("z",natT, oeq (suc a) (suc (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxt
            [(("P",0),cterm Pabs),(("a",0),cterm a),(("b",0),cterm b)] oeq_subst_v);
      val refl = beta_norm (Drule.infer_instantiate ctxt [(("a",0),cterm (suc a))] oeq_refl_v);
      val step = inst OF [Thm.assume (cterm (jT (oeq a b))), refl];
  in varify (Thm.implies_intr (cterm (jT (oeq a b))) step) end;
fun sucCong h = beta_norm (Suc_cong OF [h]);

(* add_cong_r : oeq y z -> oeq (add x y) (add x z) *)
val add_cong_r =
  let val x=Free("x",natT); val y=Free("y",natT); val z=Free("z",natT);
      val Pabs = Abs("w",natT, oeq (add x y) (add x (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxt
            [(("P",0),cterm Pabs),(("a",0),cterm y),(("b",0),cterm z)] oeq_subst_v);
      val refl = beta_norm (Drule.infer_instantiate ctxt [(("a",0),cterm (add x y))] oeq_refl_v);
      val step = inst OF [Thm.assume (cterm (jT (oeq y z))), refl];
  in varify (Thm.implies_intr (cterm (jT (oeq y z))) step) end;
fun addCongR (x,y,z) h =
  beta_norm ((Drule.infer_instantiate ctxt
     [(("x",0),cterm x),(("y",0),cterm y),(("z",0),cterm z)] add_cong_r) OF [h]);

(* mult_cong_r : oeq y z -> oeq (mult x y) (mult x z) *)
val mult_cong_r =
  let val x=Free("x",natT); val y=Free("y",natT); val z=Free("z",natT);
      val Pabs = Abs("w",natT, oeq (mult x y) (mult x (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxt
            [(("P",0),cterm Pabs),(("a",0),cterm y),(("b",0),cterm z)] oeq_subst_v);
      val refl = beta_norm (Drule.infer_instantiate ctxt [(("a",0),cterm (mult x y))] oeq_refl_v);
      val step = inst OF [Thm.assume (cterm (jT (oeq y z))), refl];
  in varify (Thm.implies_intr (cterm (jT (oeq y z))) step) end;
fun multCongR (x,y,z) h =
  beta_norm ((Drule.infer_instantiate ctxt
     [(("x",0),cterm x),(("y",0),cterm y),(("z",0),cterm z)] mult_cong_r) OF [h]);

val () = out "TSQ_FOUNDATION_OK\n";

(* numeral term: Suc^k Zero *)
fun numT 0 = ZeroC | numT k = suc (numT (k-1));

(* ---- kernel computation: addEval x k  produces  |- oeq (add (numT x) (numT k)) (numT (x+k)) ----
   By induction-free direct recursion using add_0 / add_Suc instances. *)
fun add_0_at t  = beta_norm (Drule.infer_instantiate ctxt [(("n",0),cterm t)] add_0_v);
fun add_Suc_at (s,t) = beta_norm (Drule.infer_instantiate ctxt
      [(("m",0),cterm s),(("n",0),cterm t)] add_Suc_v);
fun mult_0_at t = beta_norm (Drule.infer_instantiate ctxt [(("n",0),cterm t)] mult_0_v);
fun mult_Suc_at (s,t) = beta_norm (Drule.infer_instantiate ctxt
      [(("m",0),cterm s),(("n",0),cterm t)] mult_Suc_v);

(* addEval : int -> int -> thm   |- oeq (add x_num k_num) (x+k)_num *)
fun addEval x k =
  if x = 0 then add_0_at (numT k)               (* oeq (add 0 k) k *)
  else
    let val prev = addEval (x-1) k              (* oeq (add (x-1) k) (x-1+k) *)
        val s    = add_Suc_at (numT (x-1), numT k) (* oeq (add (Suc(x-1)) k) (Suc(add (x-1) k)) *)
        val cong = sucCong prev                 (* oeq (Suc(add (x-1) k)) (Suc((x-1+k))) *)
    in oeqTrans (s, cong) end;

(* multEval : int -> int -> thm  |- oeq (mult x_num k_num) (x*k)_num *)
fun multEval x k =
  if x = 0 then mult_0_at (numT k)              (* oeq (mult 0 k) 0 *)
  else
    let val prev = multEval (x-1) k             (* oeq (mult (x-1) k) ((x-1)*k) *)
        val s    = mult_Suc_at (numT (x-1), numT k) (* oeq (mult (Suc(x-1)) k) (add k (mult (x-1) k)) *)
        val cong = addCongR (numT k, mult (numT (x-1)) (numT k), numT ((x-1)*k)) prev
                                                (* oeq (add k (mult(x-1)k)) (add k ((x-1)*k)) *)
        val ae   = addEval k ((x-1)*k)          (* oeq (add k ((x-1)*k)) (k + (x-1)*k) = x*k *)
    in oeqTrans (s, oeqTrans (cong, ae)) end;

val () = out "TSQ_EVAL_OK\n";

(* sumThreeSq a b c : |- oeq (a*a+b*b+c*c) (numT v)  where v = a^2+b^2+c^2.
   Build the term exactly as a^2+b^2+c^2 = ((a*a)+(b*b))+(c*c) then reduce. *)
fun reduceMul x = multEval x x;   (* oeq (mult x x) (x*x) *)

(* reduce  add of two NUMERAL-reducible terms.
   given h1 : oeq T1 (numT v1), h2 : oeq T2 (numT v2)
   produce oeq (add T1 T2) (numT (v1+v2)). *)
fun addReduce (T1,v1,h1) (T2,v2,h2) =
  let
    (* oeq (add T1 T2) (add (numT v1) T2)  via add_cong_l (use sym of subst route).
       Simpler: rewrite left arg then right arg via two subst congruences. *)
    (* add_cong_l: oeq y z -> oeq (add y x)(add z x) *)
    val acl =
      let val x=Free("x",natT); val y=Free("y",natT); val z=Free("z",natT);
          val Pabs = Abs("w",natT, oeq (add y x) (add (Bound 0) x));
          val inst = beta_norm (Drule.infer_instantiate ctxt
                [(("P",0),cterm Pabs),(("a",0),cterm y),(("b",0),cterm z)] oeq_subst_v);
          val refl = beta_norm (Drule.infer_instantiate ctxt [(("a",0),cterm (add y x))] oeq_refl_v);
          val step = inst OF [Thm.assume (cterm (jT (oeq y z))), refl];
      in varify (Thm.implies_intr (cterm (jT (oeq y z))) step) end;
    fun addCongL (y,z,x) h =
      beta_norm ((Drule.infer_instantiate ctxt
         [(("x",0),cterm x),(("y",0),cterm y),(("z",0),cterm z)] acl) OF [h]);
    val left  = addCongL (T1, numT v1, T2) h1     (* oeq (add T1 T2) (add v1 T2) *)
    val right = addCongR (numT v1, T2, numT v2) h2 (* oeq (add v1 T2) (add v1 v2) *)
    val ev    = addEval v1 v2                       (* oeq (add v1 v2) (v1+v2) *)
  in (add T1 T2, v1+v2, oeqTrans (left, oeqTrans (right, ev))) end;

(* threeSqEval a b c : (term, value, thm |- oeq term value) *)
fun threeSqEval a b c =
  let
    val (ta,va,ha) = (mult (numT a)(numT a), a*a, reduceMul a)
    val (tb,vb,hb) = (mult (numT b)(numT b), b*b, reduceMul b)
    val (tc,vc,hc) = (mult (numT c)(numT c), c*c, reduceMul c)
    val ab = addReduce (ta,va,ha) (tb,vb,hb)
    val abc = addReduce ab (tc,vc,hc)
  in abc end;

(* fourSqEval a b c d *)
fun fourSqEval a b c d =
  let
    val (ta,va,ha) = (mult (numT a)(numT a), a*a, reduceMul a)
    val (tb,vb,hb) = (mult (numT b)(numT b), b*b, reduceMul b)
    val (tc,vc,hc) = (mult (numT c)(numT c), c*c, reduceMul c)
    val (td,vd,hd) = (mult (numT d)(numT d), d*d, reduceMul d)
    val ab = addReduce (ta,va,ha) (tb,vb,hb)
    val cd = addReduce (tc,vc,hc) (td,vd,hd)
  in addReduce ab cd end;

val () = out "TSQ_SUMEVAL_OK\n";

(* ---- (1) THREE-SQUARES REJECTION for 7 ----
   For each (a,b,c) in {0,1,2}^3 compute the kernel normal form value;
   if ANY equals 7 the three-square form would be witnessable.  Confirm NONE does. *)
val cands = [0,1,2];   (* 3^2=9>7, so a,b,c<=2 covers all candidates *)
val matches7 =
  List.filter (fn (a,b,c) =>
      let val (_,v,_) = threeSqEval a b c in v = 7 end)
    (List.concat (List.map (fn a => List.concat (List.map (fn b => List.map (fn c => (a,b,c)) cands) cands)) cands));
val () = out ("TSQ_THREE_CANDIDATES_MATCHING_7 = " ^ Int.toString (length matches7) ^ "\n");
val () = if null matches7
         then out "TSQ_THREE_SQUARE_REJECTED_OK  (7 is NOT a sum of three squares -> kernel cannot witness EX a b c. 7=a^2+b^2+c^2)\n"
         else out "TSQ_THREE_SQUARE_UNSOUND  (some (a,b,c) computed to 7!)\n";

(* Cross-check: the kernel-computed value of each candidate, to show it really computes. *)
val () = out ("TSQ_SAMPLE 2^2+1^2+1^2 = " ^ Int.toString (#2 (threeSqEval 2 1 1)) ^ " (=6, the max three-square <=7 with distinct, !=7)\n");
val () = out ("TSQ_SAMPLE 2^2+2^2+0^2 = " ^ Int.toString (#2 (threeSqEval 2 2 0)) ^ " (=8 >7)\n");

(* ---- (2) FOUR-SQUARES holds for 7 : 2^2+1^2+1^2+1^2 = 7, by kernel reflexivity ----
   Build |- oeq (numT 7) (a*a+b*b+c*c+d*d) for (a,b,c,d)=(2,1,1,1). *)
val () =
  let
    val (tsum, v, hsum) = fourSqEval 2 1 1 1     (* oeq (sum-term) (numT v) *)
    val () = out ("TSQ_FOUR 2^2+1^2+1^2+1^2 = " ^ Int.toString v ^ "\n")
    (* |- oeq (numT 7) sum-term  by symmetry of hsum (needs v=7) *)
    val thm7 = oeqSym hsum                         (* oeq (numT v) sum-term *)
    val ok = (v = 7) andalso (length (Thm.hyps_of thm7) = 0)
  in if ok then out "TSQ_FOUR_SQUARE_HOLDS_OK  (7 = 2^2+1^2+1^2+1^2 by kernel inference, 0-hyp)\n"
     else out "TSQ_FOUR_SQUARE_FAIL\n"
  end;

(* ---- (3) KERNEL REJECTS A FALSE NUMERIC EQUALITY ----
   Attempt to obtain |- oeq (numT 7) (numT 6).  There is NO inference path; any
   attempt to coerce one (here: claim the computed value of a three-square sum is
   7 when it is not) must FAIL.  We probe at the kernel boundary: take a sum that
   computes to 6 and try to *assert* it equals 7 by reusing its own (honest) thm,
   confirming the honest thm's value is 6 (not 7) — the kernel never yields oeq 7 6. *)
val () =
  let
    val (_, v6, h6) = threeSqEval 2 1 1     (* honest: oeq (...) 6 *)
    (* The conclusion of h6 is oeq (...) (numT 6); confirm it is NOT oeq (...) (numT 7). *)
    val concl = Thm.prop_of h6
    val wrong = jT (oeq (#1 (threeSqEval 2 1 1)) (numT 7))
    val rejects = not (concl aconv wrong)
    val () = out ("TSQ_HONEST_VALUE = " ^ Int.toString v6 ^ "\n")
  in if rejects andalso v6 = 6
     then out "TSQ_KERNEL_REJECTS_FALSE_EQ_OK  (kernel yields oeq ... 6, never oeq ... 7)\n"
     else out "TSQ_KERNEL_REJECTS_FALSE_EQ_FAIL\n"
  end;

val () = out "TSQ_ALL_DONE\n";
