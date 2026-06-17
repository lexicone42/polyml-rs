(* ============================================================================
   PRIMES =3 MOD 4 : base + KEY LEMMA  (built on ctxtF from isabelle_euclid.sml)
   ============================================================================ *)
val () = out "P3_DELTA_BEGIN\n";

(* numerals *)
val oneC   = suc ZeroC;
val twoC   = suc (suc ZeroC);
val threeC = suc (suc (suc ZeroC));
val fourC  = suc (suc (suc (suc ZeroC)));

(* ---- extra ground instantiators on ctxtF that the euclid driver did not need ---- *)
val add_comm_vF   = varify add_comm;
val add_assoc_vF2 = varify add_assoc;
val mult_assoc_vF = varify mult_assoc;
val right_distrib_vF = varify right_distrib;
val mult_0_vF2    = varify mult_0;       (* oeq (mult 0 n) 0 *)
fun addcommF_at (mt,nt)      = beta_norm (Drule.infer_instantiate ctxtF
      [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_comm_vF);
fun multassocF_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtF
      [(("m",0), ctermF mt),(("n",0), ctermF nt),(("k",0), ctermF kt)] mult_assoc_vF);
fun rdistF_at (aT,bT,kT)     = beta_norm (Drule.infer_instantiate ctxtF
      [(("m",0), ctermF aT),(("n",0), ctermF bT),(("k",0), ctermF kT)] right_distrib_vF);
fun mult0lF_at t             = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_0_vF2);

(* nat_induct ground instantiator already: nat_induct_atF (Qabs, kT) *)

(* a uniform 0-hyp + aconv checker for THIS delta, on ctxtF *)
fun checkP (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtF (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtF intended ^ "\n");
          false)
  end;

(* ============================================================================
   RESIDUE ABBREVIATIONS (additive, capture-avoiding via Term.lambda over a Free):
     r0 x == Ex t. x = 4*t          (= mult 4 t)
     r1 x == Ex t. x = 4*t + 1
     r2 x == Ex t. x = 4*t + 2
     r3 x == Ex t. x = 4*t + 3      (THE encoding of "x = 3 mod 4")
     odd  x == Ex t. x = 2*t + 1
     even x == Ex t. x = 2*t
   ============================================================================ *)
fun rk k x = mkEx (Abs ("t", natT, oeq x (add (mult fourC (Bound 0)) k)));
fun r0 x = mkEx (Abs ("t", natT, oeq x (mult fourC (Bound 0))));
fun r1 x = rk oneC x;
fun r2 x = rk twoC x;
fun r3 x = rk threeC x;
fun oddP  x = mkEx (Abs ("t", natT, oeq x (add (mult twoC (Bound 0)) oneC)));
fun evenP x = mkEx (Abs ("t", natT, oeq x (mult twoC (Bound 0))));

(* intro helpers (exI on the matching abstraction) *)
fun r0_intro (x, w) hyp =
  let val P = Abs ("t", natT, oeq x (mult fourC (Bound 0)))
  in exI_atF P w hyp end;
fun rk_intro k (x, w) hyp =
  let val P = Abs ("t", natT, oeq x (add (mult fourC (Bound 0)) k))
  in exI_atF P w hyp end;
fun r1_intro (x,w) h = rk_intro oneC   (x,w) h;
fun r2_intro (x,w) h = rk_intro twoC   (x,w) h;
fun r3_intro (x,w) h = rk_intro threeC (x,w) h;
fun odd_intro (x, w) hyp =
  let val P = Abs ("t", natT, oeq x (add (mult twoC (Bound 0)) oneC))
  in exI_atF P w hyp end;
fun even_intro (x, w) hyp =
  let val P = Abs ("t", natT, oeq x (mult twoC (Bound 0)))
  in exI_atF P w hyp end;

val () = out "P3_RESIDUE_DEFS_READY\n";

(* ============================================================================
   SMALL ARITHMETIC LEMMA : add_comm / mult_comm sanity on ctxtF.
   ============================================================================ *)
val mV3 = Var (("m",0), natT);
val nV3 = Var (("n",0), natT);
val r_addcomm_sanity =
  let
    val th = varify (addcommF_at (Free("m",natT), Free("n",natT)));
  in checkP ("addcomm_sanity", th, jT (oeq (add mV3 nV3) (add nV3 mV3))) end;

val () = if r_addcomm_sanity then out "P3_PART1_OK\n" else out "P3_PART1_FAILED\n";
(* ============================================================================
   PART 2 : arithmetic primitives + parity/residue exclusivity
   ============================================================================ *)

(* add_left_cancel on ctxtF *)
val add_left_cancelF = varify add_left_cancel;   (* oeq (add z a)(add z b) ==> oeq a b *)

(* two_mult t : oeq (mult two t) (add t t)
     mult (Suc(Suc 0)) t = add t (mult (Suc 0) t)
                         = add t (add t (mult 0 t))
                         = add t (add t 0)
                         = add t t                          *)
fun two_mult_at t =
  let
    val s1 = multSucF_at (suc ZeroC, t);          (* mult 2 t = add t (mult 1 t) *)
    val s2 = multSucF_at (ZeroC, t);              (* mult 1 t = add t (mult 0 t) *)
    val s3 = mult0lF_at t;                        (* mult 0 t = 0 *)
    val s2' = oeq_trans OF [s2, add_cong_rF (t, mult ZeroC t, ZeroC) s3];  (* mult 1 t = add t 0 *)
    val s2'' = oeq_trans OF [s2', add0rF_at t];   (* mult 1 t = t *)
    val cong = add_cong_rF (t, mult oneC t, t) s2''; (* add t (mult 1 t) = add t t *)
  in oeq_trans OF [s1, cong] end;                 (* mult 2 t = add t t *)

(* four_mult t : oeq (mult four t) (add (mult two t) (mult two t))
     mult 4 t = add t (mult 3 t) = ... ; easier: 4 = 2+2, right_distrib:
       mult (add 2 2) t = add (mult 2 t)(mult 2 t), and (add 2 2) = 4.        *)
val two_plus_two =
  let
    val a1 = addSucF_at (suc ZeroC, twoC);        (* (Suc(Suc 0)) + 2 = Suc((Suc 0)+2) *)
    val a2 = addSucF_at (ZeroC, twoC);            (* (Suc 0)+2 = Suc(0+2) *)
    val a3 = add0F_at twoC;                       (* 0+2 = 2 *)
    val sa3 = Suc_cong OF [a3];                   (* Suc(0+2) = Suc 2 = 3 *)
    val sa2 = Suc_cong OF [oeq_trans OF [a2, sa3]];  (* Suc((Suc 0)+2) = Suc 3 = 4 *)
  in oeq_trans OF [a1, sa2] end;                  (* (2 + 2) = 4 *)
(* so oeq (add two two) four *)

fun four_mult_at t =
  let
    val rd  = rdistF_at (twoC, twoC, t);          (* mult (add 2 2) t = add (mult 2 t)(mult 2 t) *)
    (* rewrite (add 2 2) -> 4 on the LHS argument: mult (add 2 2) t = mult 4 t *)
    val zF  = Free("z_fm", natT);
    val Psub = Term.lambda zF (oeq (mult (add twoC twoC) t) (mult zF t));
    val subI = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Psub), (("a",0), ctermF (add twoC twoC)), (("b",0), ctermF fourC)] oeq_subst_vF);
    val reflL = oeqreflF_at (mult (add twoC twoC) t);
    val m22_m4 = subI OF [two_plus_two, reflL];   (* mult (add 2 2) t = mult 4 t *)
    val m4_m22 = oeq_sym OF [m22_m4];             (* mult 4 t = mult (add 2 2) t *)
  in oeq_trans OF [m4_m22, rd] end;               (* mult 4 t = add (mult 2 t)(mult 2 t) *)

val () = out "P3_ARITH_PRIMS_READY\n";

(* ============================================================================
   one_ne_double : oeq (Suc Zero) (mult two e) ==> oFalse        (1 = 2e impossible)
     2e = e + e (two_mult).  cases on e (dzosF):
       e = 0     : 2e = 0+0 = 0 ; 1 = 0 -> Suc 0 = 0 -> Suc_neq_Zero.
       e = Suc f : 2e = add (Suc f)(Suc f) = Suc(...) ; 1 = Suc(...) -> Suc_inj -> 0 = Suc(..) -> False.
   ============================================================================ *)
val one_ne_double =
  let
    val eF = Free("e", natT);
    val hyp = Thm.assume (ctermF (jT (oeq oneC (mult twoC eF))));   (* 1 = mult 2 e *)
    val tm  = two_mult_at eF;                                       (* mult 2 e = add e e *)
    val one_ee = oeq_trans OF [hyp, tm];                            (* 1 = add e e *)
    val dz = dzosF_at eF;                                           (* Disj (oeq e 0)(Ex q. oeq e (Suc q)) *)
    val caseZ =
      let
        val hz = Thm.assume (ctermF (jT (oeq eF ZeroC)));           (* e = 0 *)
        (* add e e = add 0 0 = 0 *)
        val c1 = add_cong_lF (eF, ZeroC, eF) hz;                    (* add e e = add 0 e *)
        val c2 = add_cong_rF (ZeroC, eF, ZeroC) hz;                 (* add 0 e = add 0 0 *)
        val a00 = add0F_at ZeroC;                                   (* add 0 0 = 0 *)
        val ee_0 = oeq_trans OF [oeq_trans OF [c1, c2], a00];       (* add e e = 0 *)
        val one_0 = oeq_trans OF [one_ee, ee_0];                    (* 1 = 0 ; i.e. Suc 0 = 0 *)
        val s0_0 = one_0;                                           (* Suc 0 = 0 *)
        val fls = (Suc_neq_ZeroF_at ZeroC) OF [s0_0];               (* oFalse *)
      in Thm.implies_intr (ctermF (jT (oeq eF ZeroC))) fls end;
    val PsucE = Abs("q", natT, oeq eF (suc (Bound 0)));
    val caseS =
      let
        val exq = Thm.assume (ctermF (jT (mkEx PsucE)));
        fun sBody q (hq : thm) =                                    (* hq : e = Suc q *)
          let
            (* add e e = add (Suc q) e = Suc (add q e) *)
            val c1 = add_cong_lF (eF, suc q, eF) hq;                (* add e e = add (Suc q) e *)
            val aS = addSucF_at (q, eF);                            (* add (Suc q) e = Suc(add q e) *)
            val ee_S = oeq_trans OF [c1, aS];                       (* add e e = Suc(add q e) *)
            val one_S = oeq_trans OF [one_ee, ee_S];                (* Suc 0 = Suc(add q e) *)
            val inj = (Suc_inj_atF (ZeroC, add q eF)) OF [one_S];   (* 0 = add q e *)
            (* but also e = Suc q so add q e = add q (Suc q) = Suc(add q q) ... actually
               we have 0 = add q e ; rewrite e = Suc q : add q e = add q (Suc q) *)
            val cqe = add_cong_rF (q, eF, suc q) hq;                (* add q e = add q (Suc q) *)
            val z_qSq = oeq_trans OF [inj, cqe];                    (* 0 = add q (Suc q) *)
            val aSr = addSrF_at (q, q);                             (* add q (Suc q) = Suc(add q q) *)
            val z_S2 = oeq_trans OF [z_qSq, aSr];                   (* 0 = Suc(add q q) *)
            val S2_z = oeq_sym OF [z_S2];                           (* Suc(add q q) = 0 *)
            val fls = (Suc_neq_ZeroF_at (add q q)) OF [S2_z];       (* oFalse *)
          in fls end;
        val g = exE_elimF (PsucE, oFalseC) exq "q0" sBody;
      in Thm.implies_intr (ctermF (jT (mkEx PsucE))) g end;
    val concl = disjE_elimF (oeq eF ZeroC, mkEx PsucE, oFalseC) dz caseZ caseS;
    val disch = Thm.implies_intr (ctermF (jT (oeq oneC (mult twoC eF)))) concl;
  in varify disch end;

val eVod = Var (("e",0), natT);
val r_one_ne_double = checkP ("one_ne_double", one_ne_double,
    Logic.mk_implies (jT (oeq oneC (mult twoC eVod)), jT oFalseC));

val () = if r_one_ne_double then out "P3_PART2_OK\n" else out "P3_PART2_FAILED\n";
(* ============================================================================
   PART 3 : parity lemmas (odd/even) and residue->parity
   ============================================================================ *)
val left_distribF2_at = left_distribF_at;   (* (x*(m+n)) = (x*m)+(x*n) *)
val one_ne_double_v = varify one_ne_double;
fun one_ne_double_at e h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("e",0), ctermF e)] one_ne_double_v)) h;

(* odd_even_False : oddP x ==> evenP x ==> oFalse
     x = add (mult 2 a) 1  and  x = mult 2 b.  So  add (mult 2 a) 1 = mult 2 b.
     le_total a b:
       a<=b : b = a+e ; mult 2 b = mult 2 (a+e) = (2a)+(2e) ;
              add (2a) 1 = add (2a)(2e) -> cancel -> 1 = 2e -> one_ne_double.
       b<=a : a = b+e ; add (2a) 1 = add (2(b+e)) 1 = add ((2b)+(2e)) 1
                       = add (2b) ((2e)+1)  (assoc) ; = mult 2 b = add (2b) 0 ;
              cancel -> add (2e) 1 = 0 ; add (2e) 1 = Suc(...) -> Suc_neq_Zero.
   ============================================================================ *)
val odd_even_False =
  let
    val xF = Free("x", natT);
    val oddP_x  = oddP xF;
    val evenP_x = evenP xF;
    val hOdd  = Thm.assume (ctermF (jT oddP_x));
    val hEven = Thm.assume (ctermF (jT evenP_x));
    val Podd  = Abs("a", natT, oeq xF (add (mult twoC (Bound 0)) oneC));
    val Peven = Abs("b", natT, oeq xF (mult twoC (Bound 0)));
    val goalC = oFalseC;
    fun bodyA aT (ha : thm) =                          (* ha : x = add (mult 2 a) 1 *)
      let
        fun bodyB bT (hb : thm) =                      (* hb : x = mult 2 b *)
          let
            (* add (2a) 1 = x = (2b) *)
            val ha_s = oeq_sym OF [ha];                (* add(2a)1 = x *)
            val key  = oeq_trans OF [ha_s, hb];        (* add (2a) 1 = mult 2 b *)
            val dz   = le_totalF_at (aT, bT);          (* Disj (le a b)(le b a) *)
            val caseAB =
              let
                val hle = Thm.assume (ctermF (jT (le aT bT)));
                val Pe  = Abs("e", natT, oeq bT (add aT (Bound 0)));   (* le a b body *)
                fun eBody eT (he : thm) =              (* he : b = add a e *)
                  let
                    val cong2b = mult_cong_rF (twoC, bT, add aT eT) he;  (* (2b) = 2*(a+e) *)
                    val ld     = left_distribF2_at (twoC, aT, eT);       (* 2*(a+e) = (2a)+(2e) *)
                    val twob_dist = oeq_trans OF [cong2b, ld];           (* (2b) = (2a)+(2e) *)
                    (* add(2a)1 = (2b) = (2a)+(2e) *)
                    val eq1 = oeq_trans OF [key, twob_dist];             (* add(2a)1 = add(2a)(2e) *)
                    val canc = add_left_cancelF OF [eq1];                (* 1 = (2e) *)
                    val fls = one_ne_double_at eT canc;                  (* oFalse *)
                  in fls end;
                val fls = exE_elimF (Pe, goalC) hle "e0" eBody;
              in Thm.implies_intr (ctermF (jT (le aT bT))) fls end;
            val caseBA =
              let
                val hle = Thm.assume (ctermF (jT (le bT aT)));
                val Pe  = Abs("e", natT, oeq aT (add bT (Bound 0)));   (* le b a body *)
                fun eBody eT (he : thm) =              (* he : a = add b e *)
                  let
                    (* (2a) = 2*(b+e) = (2b)+(2e) *)
                    val cong2a = mult_cong_rF (twoC, aT, add bT eT) he;   (* (2a) = 2*(b+e) *)
                    val ld     = left_distribF2_at (twoC, bT, eT);        (* 2*(b+e) = (2b)+(2e) *)
                    val twoa_dist = oeq_trans OF [cong2a, ld];            (* (2a) = (2b)+(2e) *)
                    (* add (2a) 1 = add ((2b)+(2e)) 1 *)
                    val cl = add_cong_lF (mult twoC aT, add (mult twoC bT) (mult twoC eT), oneC) twoa_dist;
                                                                         (* add(2a)1 = add((2b)+(2e))1 *)
                    val asc = addassocF_at (mult twoC bT, mult twoC eT, oneC);
                                                                         (* add((2b)+(2e))1 = add(2b)((2e)+1) *)
                    val lhs = oeq_trans OF [cl, asc];                    (* add(2a)1 = add(2b)((2e)+1) *)
                    (* key: add(2a)1 = (2b) ; and (2b) = add(2b)0 *)
                    val rhs0 = oeq_sym OF [add0rF_at (mult twoC bT)];    (* (2b) = add(2b)0 *)
                    val key0 = oeq_trans OF [key, rhs0];                 (* add(2a)1 = add(2b)0 *)
                    (* combine : add(2b)((2e)+1) = add(2b)0 *)
                    val eqB = oeq_trans OF [oeq_sym OF [lhs], key0];     (* add(2b)((2e)+1) = add(2b)0 *)
                    val canc = add_left_cancelF OF [eqB];               (* (2e)+1 = 0 *)
                    (* (2e)+1 = Suc(2e+0)=Suc(2e) ... actually (2e)+1 = (2e)+(Suc 0) = Suc((2e)+0) *)
                    val aSr = addSrF_at (mult twoC eT, ZeroC);          (* (2e)+(Suc 0) = Suc((2e)+0) *)
                    val a0  = add0rF_at (mult twoC eT);                 (* (2e)+0 = (2e) *)
                    val sa0 = Suc_cong OF [a0];                         (* Suc((2e)+0) = Suc(2e) *)
                    val twoe1_S = oeq_trans OF [aSr, sa0];              (* (2e)+1 = Suc(2e) *)
                    val S_eq0 = oeq_trans OF [oeq_sym OF [twoe1_S], canc]; (* Suc(2e) = 0 *)
                    val fls = (Suc_neq_ZeroF_at (mult twoC eT)) OF [S_eq0]; (* oFalse *)
                  in fls end;
                val fls = exE_elimF (Pe, goalC) hle "e0" eBody;
              in Thm.implies_intr (ctermF (jT (le bT aT))) fls end;
            val combined = disjE_elimF (le aT bT, le bT aT, goalC) dz caseAB caseBA;
          in combined end;
        val g = exE_elimF (Peven, goalC) hEven "b0" bodyB;
      in g end;
    val res = exE_elimF (Podd, goalC) hOdd "a0" bodyA;
    val d2 = Thm.implies_intr (ctermF (jT evenP_x)) res;
    val d1 = Thm.implies_intr (ctermF (jT oddP_x)) d2;
  in varify d1 end;

val xVoe = Var (("x",0), natT);
val r_odd_even_False = checkP ("odd_even_False", odd_even_False,
    Logic.mk_implies (jT (oddP xVoe), Logic.mk_implies (jT (evenP xVoe), jT oFalseC)));

val () = if r_odd_even_False then out "P3_PART3_OK\n" else out "P3_PART3_FAILED\n";
(* ============================================================================
   PART 4 : residue -> parity + even_mult
   ============================================================================ *)

(* mult 2 (Suc 0) = 2  : helper to evaluate mult 2 1 = 2 *)
val mult2_1 =
  let
    val tm = two_mult_at oneC;                 (* mult 2 1 = add 1 1 *)
    val a1 = addSucF_at (ZeroC, oneC);         (* (Suc 0 + 1) = Suc(0+1) *)
    val a0 = add0F_at oneC;                    (* 0 + 1 = 1 *)
    val sa = Suc_cong OF [a0];                 (* Suc(0+1) = Suc 1 = 2 *)
    val one1_2 = oeq_trans OF [a1, sa];        (* add 1 1 = 2 *)
  in oeq_trans OF [tm, one1_2] end;            (* mult 2 1 = 2 *)

(* r0_imp_even : r0 x ==> evenP x   (x = 4t = 2*(2t)) *)
val r0_imp_even =
  let
    val xF = Free("x", natT);
    val hr0 = Thm.assume (ctermF (jT (r0 xF)));
    val P0  = Abs("t", natT, oeq xF (mult fourC (Bound 0)));
    fun body t (ht : thm) =                     (* ht : x = mult 4 t *)
      let
        val fm = four_mult_at t;               (* mult 4 t = add (mult 2 t)(mult 2 t) *)
        val tm = two_mult_at (mult twoC t);    (* mult 2 (2t) = add (2t)(2t) *)
        val tms = oeq_sym OF [tm];             (* add (2t)(2t) = mult 2 (2t) *)
        val x_4t = ht;                         (* x = mult 4 t *)
        val x_sum = oeq_trans OF [x_4t, fm];   (* x = add (2t)(2t) *)
        val x_2_2t = oeq_trans OF [x_sum, tms];(* x = mult 2 (2t) *)
      in even_intro (xF, mult twoC t) x_2_2t end;  (* evenP x, witness 2t *)
    val g = exE_elimF (P0, evenP xF) hr0 "t0" body;
    val disch = Thm.implies_intr (ctermF (jT (r0 xF))) g;
  in varify disch end;

(* r2_imp_even : r2 x ==> evenP x   (x = 4t+2 = 2*(2t+1)) *)
val r2_imp_even =
  let
    val xF = Free("x", natT);
    val hr2 = Thm.assume (ctermF (jT (r2 xF)));
    val P2  = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) twoC));
    fun body t (ht : thm) =                     (* ht : x = add (mult 4 t) 2 *)
      let
        val wit = add (mult twoC t) oneC;       (* 2t+1 *)
        (* 2*(2t+1) = (2*(2t)) + (2*1) = (add (2t)(2t)) + 2 = (mult 4 t) + 2 *)
        val ld  = left_distribF2_at (twoC, mult twoC t, oneC);  (* 2*(2t+1) = (2*(2t)) + (2*1) *)
        val tm2t = two_mult_at (mult twoC t);   (* 2*(2t) = (2t)+(2t) *)
        val fm  = four_mult_at t;               (* 4t = (2t)+(2t) *)
        val fms = oeq_sym OF [fm];              (* (2t)+(2t) = 4t *)
        val tm2t_4t = oeq_trans OF [tm2t, fms]; (* 2*(2t) = 4t *)
        val cl = add_cong_lF (mult twoC (mult twoC t), mult fourC t, mult twoC oneC) tm2t_4t;
                                                (* (2*(2t))+(2*1) = (4t)+(2*1) *)
        val cr = add_cong_rF (mult fourC t, mult twoC oneC, twoC) mult2_1;
                                                (* (4t)+(2*1) = (4t)+2 *)
        val rhs = oeq_trans OF [oeq_trans OF [ld, cl], cr];  (* 2*(2t+1) = (4t)+2 *)
        val rhss = oeq_sym OF [rhs];            (* (4t)+2 = 2*(2t+1) *)
        val x_2wit = oeq_trans OF [ht, rhss];   (* x = 2*(2t+1) *)
      in even_intro (xF, wit) x_2wit end;
    val g = exE_elimF (P2, evenP xF) hr2 "t0" body;
    val disch = Thm.implies_intr (ctermF (jT (r2 xF))) g;
  in varify disch end;

(* r3_imp_odd : r3 x ==> oddP x   (x = 4t+3 = 2*(2t+1)+1) *)
val r3_imp_odd =
  let
    val xF = Free("x", natT);
    val hr3 = Thm.assume (ctermF (jT (r3 xF)));
    val P3  = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) threeC));
    fun body t (ht : thm) =                     (* ht : x = add (mult 4 t) 3 *)
      let
        val wit = add (mult twoC t) oneC;       (* a = 2t+1 *)
        (* (2a)+1 = (2*(2t+1))+1 = ((4t)+2)+1 = (4t)+(2+1) = (4t)+3 *)
        (* reuse r2 computation : 2*(2t+1) = (4t)+2 *)
        val ld  = left_distribF2_at (twoC, mult twoC t, oneC);  (* 2*(2t+1) = (2*(2t))+(2*1) *)
        val tm2t = two_mult_at (mult twoC t);
        val fm  = four_mult_at t;
        val tm2t_4t = oeq_trans OF [tm2t, oeq_sym OF [fm]];     (* 2*(2t) = 4t *)
        val cl = add_cong_lF (mult twoC (mult twoC t), mult fourC t, mult twoC oneC) tm2t_4t;
        val cr = add_cong_rF (mult fourC t, mult twoC oneC, twoC) mult2_1;
        val two_a = oeq_trans OF [oeq_trans OF [ld, cl], cr];   (* 2*(2t+1) = (4t)+2 *)
        (* (2a)+1 = ((4t)+2)+1 *)
        val cl1 = add_cong_lF (mult twoC wit, add (mult fourC t) twoC, oneC) two_a;
                                                (* (2*(2t+1))+1 = ((4t)+2)+1 *)
        val asc = addassocF_at (mult fourC t, twoC, oneC);      (* ((4t)+2)+1 = (4t)+(2+1) *)
        (* 2+1 = 3 *)
        val a21 = addSucF_at (oneC, oneC);      (* (Suc 0 + 1)... wait 2 = Suc 1; (Suc 1)+1 = Suc(1+1) *)
        (* compute 2+1 = 3 : add 2 1 = add (Suc 1) 1 = Suc(1+1) = Suc 2 = 3 *)
        val a21b = addSucF_at (oneC, oneC);     (* (Suc 1 + 1) = Suc(1 + 1) *)
        val a11  = addSucF_at (ZeroC, oneC);    (* (Suc 0 + 1) = Suc(0+1) *)
        val a01  = add0F_at oneC;               (* 0+1 = 1 *)
        val s01  = Suc_cong OF [a01];           (* Suc(0+1) = 2 *)
        val one1_2 = oeq_trans OF [a11, s01];   (* (1+1) = 2 *)
        val two1_3 = oeq_trans OF [a21b, Suc_cong OF [one1_2]]; (* (2+1) = 3 *)
        val cr2 = add_cong_rF (mult fourC t, add twoC oneC, threeC) two1_3;
                                                (* (4t)+(2+1) = (4t)+3 *)
        val rhs = oeq_trans OF [oeq_trans OF [cl1, asc], cr2];  (* (2*(2t+1))+1 = (4t)+3 *)
        val rhss = oeq_sym OF [rhs];            (* (4t)+3 = (2*(2t+1))+1 *)
        val x_form = oeq_trans OF [ht, rhss];   (* x = (2*(2t+1))+1 = add (mult 2 wit) 1 *)
      in odd_intro (xF, wit) x_form end;
    val g = exE_elimF (P3, oddP xF) hr3 "t0" body;
    val disch = Thm.implies_intr (ctermF (jT (r3 xF))) g;
  in varify disch end;

(* even_mult : evenP a ==> evenP (mult a b)   (a = 2s ==> ab = 2(sb)) *)
val even_mult =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hEv = Thm.assume (ctermF (jT (evenP aF)));
    val Pe  = Abs("s", natT, oeq aF (mult twoC (Bound 0)));
    fun body s (hs : thm) =                      (* hs : a = mult 2 s *)
      let
        (* ab = (2s)*b = 2*(s*b)  via mult_cong_l then mult_assoc *)
        val cong = mult_cong_lF (aF, mult twoC s, bF) hs;   (* ab = (2s)*b *)
        val asc  = multassocF_at (twoC, s, bF);             (* (2*s)*b = 2*(s*b) *)
        val ab_form = oeq_trans OF [cong, asc];             (* ab = 2*(s*b) *)
      in even_intro (mult aF bF, mult s bF) ab_form end;    (* evenP (ab), witness s*b *)
    val g = exE_elimF (Pe, evenP (mult aF bF)) hEv "s0" body;
    val disch = Thm.implies_intr (ctermF (jT (evenP aF))) g;
  in varify disch end;

val xVr = Var (("x",0), natT);
val aVr = Var (("a",0), natT);
val bVr = Var (("b",0), natT);
val r_r0_even = checkP ("r0_imp_even", r0_imp_even, Logic.mk_implies (jT (r0 xVr), jT (evenP xVr)));
val r_r2_even = checkP ("r2_imp_even", r2_imp_even, Logic.mk_implies (jT (r2 xVr), jT (evenP xVr)));
val r_r3_odd  = checkP ("r3_imp_odd",  r3_imp_odd,  Logic.mk_implies (jT (r3 xVr), jT (oddP xVr)));
val r_even_mult = checkP ("even_mult", even_mult,
    Logic.mk_implies (jT (evenP aVr), jT (evenP (mult aVr bVr))));

val () = if r_r0_even andalso r_r2_even andalso r_r3_odd andalso r_even_mult
         then out "P3_PART4_OK\n" else out "P3_PART4_FAILED\n";
(* ============================================================================
   PART 5 : mod4_cases (induction) + even_or_odd + odd_imp_r1_or_r3
   ============================================================================ *)

(* suc_as_add1 y : oeq (suc y) (add y 1)
     add y (Suc 0) = Suc(add y 0) = Suc y  ; so (add y 1) = (suc y) ; sym. *)
fun suc_as_add1_at y =
  let
    val aSr = addSrF_at (y, ZeroC);          (* (y + Suc 0) = Suc(y + 0) *)
    val a0  = add0rF_at y;                    (* (y + 0) = y *)
    val sa0 = Suc_cong OF [a0];               (* Suc(y+0) = Suc y *)
    val y1_Sy = oeq_trans OF [aSr, sa0];      (* (y + 1) = Suc y *)
  in oeq_sym OF [y1_Sy] end;                  (* Suc y = (y + 1) *)

(* add_y_Suc_to_succ_add : Suc(add y k) = add y (Suc k)  i.e. sym of addSr *)
fun suc_add_at (y, k) = oeq_sym OF [addSrF_at (y, k)];   (* Suc(add y k) = add y (Suc k) *)

(* nested 4-way disjunction *)
fun disj4 x = mkDisj (r0 x) (mkDisj (r1 x) (mkDisj (r2 x) (r3 x)));

(* injection helpers into disj4 z (z a Free/term) *)
fun inj_r0 z h = disjI1F_at (r0 z, mkDisj (r1 z) (mkDisj (r2 z) (r3 z))) h;
fun inj_r1 z h = disjI2F_at (r0 z, mkDisj (r1 z) (mkDisj (r2 z) (r3 z)))
                   (disjI1F_at (r1 z, mkDisj (r2 z) (r3 z)) h);
fun inj_r2 z h = disjI2F_at (r0 z, mkDisj (r1 z) (mkDisj (r2 z) (r3 z)))
                   (disjI2F_at (r1 z, mkDisj (r2 z) (r3 z))
                      (disjI1F_at (r2 z, r3 z) h));
fun inj_r3 z h = disjI2F_at (r0 z, mkDisj (r1 z) (mkDisj (r2 z) (r3 z)))
                   (disjI2F_at (r1 z, mkDisj (r2 z) (r3 z))
                      (disjI2F_at (r2 z, r3 z) h));

val mod4_cases =
  let
    val zF0 = Free("zz", natT);
    val Qpred = Term.lambda zF0 (disj4 zF0);
    val kF = Free("x", natT);
    val ind = nat_induct_atF (Qpred, kF);

    (* BASE : disj4 0 ; r0 0 witness 0 : 0 = mult 4 0 *)
    val base =
      let
        val m40 = mult0rF_at fourC;            (* mult 4 0 = 0 *)
        val z_eq = oeq_sym OF [m40];           (* 0 = mult 4 0 *)
        val r00 = r0_intro (ZeroC, ZeroC) z_eq;(* r0 0 *)
      in inj_r0 ZeroC r00 end;

    (* STEP : disj4 x ==> disj4 (Suc x) *)
    val xF = Free("x_s", natT);
    val ihprop = jT (disj4 xF);
    val IH = Thm.assume (ctermF ihprop);
    val goalC = disj4 (suc xF);

    (* case r0 x : x = 4t ; Suc x = (4t)+1 = r1 (Suc x) witness t *)
    val caseR0 =
      let
        val h = Thm.assume (ctermF (jT (r0 xF)));
        val P = Abs("t", natT, oeq xF (mult fourC (Bound 0)));
        fun body t (ht : thm) =                 (* x = mult 4 t *)
          let
            val sx = suc_as_add1_at xF;         (* Suc x = (x + 1) *)
            (* x+1 = (4t)+1 *)
            val cl = add_cong_lF (xF, mult fourC t, oneC) ht;  (* (x+1) = ((4t)+1) *)
            val form = oeq_trans OF [sx, cl];   (* Suc x = (4t)+1 *)
            val r1Sx = r1_intro (suc xF, t) form;
          in inj_r1 (suc xF) r1Sx end;
        val g = exE_elimF (P, goalC) h "t0" body;
      in Thm.implies_intr (ctermF (jT (r0 xF))) g end;

    (* case r1 x : x = (4t)+1 ; Suc x = (4t)+2 *)
    val caseR1 =
      let
        val h = Thm.assume (ctermF (jT (r1 xF)));
        val P = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) oneC));
        fun body t (ht : thm) =                 (* x = (4t)+1 *)
          let
            val sx = suc_as_add1_at xF;         (* Suc x = x+1 *)
            val cl = add_cong_lF (xF, add (mult fourC t) oneC, oneC) ht;  (* x+1 = ((4t)+1)+1 *)
            val asc = addassocF_at (mult fourC t, oneC, oneC);            (* ((4t)+1)+1 = (4t)+(1+1) *)
            (* 1+1 = 2 *)
            val a11 = addSucF_at (ZeroC, oneC); val a01 = add0F_at oneC;
            val one1_2 = oeq_trans OF [a11, Suc_cong OF [a01]];           (* (1+1) = 2 *)
            val cr = add_cong_rF (mult fourC t, add oneC oneC, twoC) one1_2;  (* (4t)+(1+1)=(4t)+2 *)
            val form = oeq_trans OF [oeq_trans OF [oeq_trans OF [sx, cl], asc], cr]; (* Suc x = (4t)+2 *)
            val r2Sx = r2_intro (suc xF, t) form;
          in inj_r2 (suc xF) r2Sx end;
        val g = exE_elimF (P, goalC) h "t0" body;
      in Thm.implies_intr (ctermF (jT (r1 xF))) g end;

    (* case r2 x : x = (4t)+2 ; Suc x = (4t)+3 *)
    val caseR2 =
      let
        val h = Thm.assume (ctermF (jT (r2 xF)));
        val P = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) twoC));
        fun body t (ht : thm) =                 (* x = (4t)+2 *)
          let
            val sx = suc_as_add1_at xF;
            val cl = add_cong_lF (xF, add (mult fourC t) twoC, oneC) ht;  (* x+1 = ((4t)+2)+1 *)
            val asc = addassocF_at (mult fourC t, twoC, oneC);           (* = (4t)+(2+1) *)
            (* 2+1 = 3 *)
            val a21 = addSucF_at (oneC, oneC); val a11 = addSucF_at (ZeroC, oneC); val a01 = add0F_at oneC;
            val one1_2 = oeq_trans OF [a11, Suc_cong OF [a01]];          (* (1+1) = 2 *)
            val two1_3 = oeq_trans OF [a21, Suc_cong OF [one1_2]];       (* (2+1) = 3 *)
            val cr = add_cong_rF (mult fourC t, add twoC oneC, threeC) two1_3;  (* (4t)+(2+1)=(4t)+3 *)
            val form = oeq_trans OF [oeq_trans OF [oeq_trans OF [sx, cl], asc], cr]; (* Suc x = (4t)+3 *)
            val r3Sx = r3_intro (suc xF, t) form;
          in inj_r3 (suc xF) r3Sx end;
        val g = exE_elimF (P, goalC) h "t0" body;
      in Thm.implies_intr (ctermF (jT (r2 xF))) g end;

    (* case r3 x : x = (4t)+3 ; Suc x = (4(Suc t)) = mult 4 (Suc t) *)
    val caseR3 =
      let
        val h = Thm.assume (ctermF (jT (r3 xF)));
        val P = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) threeC));
        fun body t (ht : thm) =                 (* x = (4t)+3 *)
          let
            (* Suc x = Suc((4t)+3) = (4t)+4  (suc_add) ; = add 4 (4t) (comm) = mult 4 (Suc t) *)
            val cong = Suc_cong OF [ht];        (* Suc x = Suc((4t)+3) *)
            (* Suc((4t)+3) = (4t)+(Suc 3) = (4t)+4 *)
            val sadd = suc_add_at (mult fourC t, threeC);  (* Suc((4t)+3) = (4t)+(Suc 3) = (4t)+4 *)
            val ft4 = oeq_trans OF [cong, sadd];           (* Suc x = (4t)+4 *)
            (* (4t)+4 = add 4 (4t) (comm) *)
            val comm = addcommF_at (mult fourC t, fourC);  (* (4t)+4 = 4+(4t) *)
            (* 4+(4t) = mult 4 (Suc t) : mult_Suc_right mult 4 (Suc t) = add 4 (mult 4 t) *)
            val msr = multSrF_at (fourC, t);               (* mult 4 (Suc t) = add 4 (mult 4 t) *)
            val msrs = oeq_sym OF [msr];                   (* add 4 (4t) = mult 4 (Suc t) *)
            val form = oeq_trans OF [oeq_trans OF [ft4, comm], msrs];  (* Suc x = mult 4 (Suc t) *)
            val r0Sx = r0_intro (suc xF, suc t) form;
          in inj_r0 (suc xF) r0Sx end;
        val g = exE_elimF (P, goalC) h "t0" body;
      in Thm.implies_intr (ctermF (jT (r3 xF))) g end;

    (* combine via nested disjE on IH = disj4 x *)
    val inner23 = mkDisj (r2 xF) (r3 xF);
    val inner123 = mkDisj (r1 xF) inner23;
    val step_r1r2r3 =
      let
        (* given Disj (r1 x)(Disj (r2 x)(r3 x)) -> goal *)
        val h123 = Thm.assume (ctermF (jT inner123));
        val step_r2r3 =
          let
            val h23 = Thm.assume (ctermF (jT inner23));
            val g = disjE_elimF (r2 xF, r3 xF, goalC) h23 caseR2 caseR3;
          in Thm.implies_intr (ctermF (jT inner23)) g end;
        val g = disjE_elimF (r1 xF, inner23, goalC) h123 caseR1 step_r2r3;
      in Thm.implies_intr (ctermF (jT inner123)) g end;
    val stepconcl = disjE_elimF (r0 xF, inner123, goalC) IH caseR0 step_r1r2r3;
    val step1 = Thm.forall_intr (ctermF xF) (Thm.implies_intr (ctermF ihprop) stepconcl);
    val r1' = Thm.implies_elim ind base;
    val r2' = Thm.implies_elim r1' step1;
  in varify r2' end;

val xVm4 = Var (("x",0), natT);
val r_mod4_cases = checkP ("mod4_cases", mod4_cases, jT (disj4 xVm4));

val () = if r_mod4_cases then out "P3_PART5_OK\n" else out "P3_PART5_FAILED\n";
(* ============================================================================
   PART 6 : even_or_odd, odd_imp_r1_or_r3, odd_mult_left
   ============================================================================ *)

(* r1_imp_odd : r1 x ==> oddP x   (x = 4t+1 = 2*(2t)+1, witness a = 2t) *)
val r1_imp_odd =
  let
    val xF = Free("x", natT);
    val h = Thm.assume (ctermF (jT (r1 xF)));
    val P = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) oneC));
    fun body t (ht : thm) =                       (* x = (4t)+1 *)
      let
        (* (4t) = 2*(2t) : four_mult 4t = (2t)+(2t) ; two_mult 2*(2t) = (2t)+(2t) ; chain *)
        val fm = four_mult_at t;                  (* 4t = (2t)+(2t) *)
        val tm = two_mult_at (mult twoC t);       (* 2*(2t) = (2t)+(2t) *)
        val t4_22t = oeq_trans OF [fm, oeq_sym OF [tm]];  (* 4t = 2*(2t) *)
        val cl = add_cong_lF (mult fourC t, mult twoC (mult twoC t), oneC) t4_22t;
                                                  (* (4t)+1 = (2*(2t))+1 *)
        val form = oeq_trans OF [ht, cl];         (* x = (2*(2t))+1 = add (mult 2 (2t)) 1 *)
      in odd_intro (xF, mult twoC t) form end;    (* oddP x, witness 2t *)
    val g = exE_elimF (P, oddP xF) h "t0" body;
  in varify (Thm.implies_intr (ctermF (jT (r1 xF))) g) end;

(* even_or_odd : Disj (evenP x)(oddP x)  from mod4_cases *)
val mod4_cases_v = varify mod4_cases;
fun mod4_cases_at x = beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] mod4_cases_v);
val r0_imp_even_v = varify r0_imp_even;
val r2_imp_even_v = varify r2_imp_even;
val r3_imp_odd_v  = varify r3_imp_odd;
val r1_imp_odd_v  = varify r1_imp_odd;
fun r0_even_at x h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r0_imp_even_v)) h;
fun r2_even_at x h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r2_imp_even_v)) h;
fun r3_odd_at  x h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r3_imp_odd_v)) h;
fun r1_odd_at  x h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r1_imp_odd_v)) h;

val even_or_odd =
  let
    val xF = Free("x", natT);
    val d4 = mod4_cases_at xF;                     (* Disj(r0)(Disj(r1)(Disj(r2)(r3))) *)
    val goalC = mkDisj (evenP xF) (oddP xF);
    val caseR0 =
      let val h = Thm.assume (ctermF (jT (r0 xF)))
      in Thm.implies_intr (ctermF (jT (r0 xF)))
           (disjI1F_at (evenP xF, oddP xF) (r0_even_at xF h)) end;
    val caseR1 =
      let val h = Thm.assume (ctermF (jT (r1 xF)))
      in Thm.implies_intr (ctermF (jT (r1 xF)))
           (disjI2F_at (evenP xF, oddP xF) (r1_odd_at xF h)) end;
    val caseR2 =
      let val h = Thm.assume (ctermF (jT (r2 xF)))
      in Thm.implies_intr (ctermF (jT (r2 xF)))
           (disjI1F_at (evenP xF, oddP xF) (r2_even_at xF h)) end;
    val caseR3 =
      let val h = Thm.assume (ctermF (jT (r3 xF)))
      in Thm.implies_intr (ctermF (jT (r3 xF)))
           (disjI2F_at (evenP xF, oddP xF) (r3_odd_at xF h)) end;
    val inner23 = mkDisj (r2 xF) (r3 xF);
    val inner123 = mkDisj (r1 xF) inner23;
    val step23 =
      let val h = Thm.assume (ctermF (jT inner23))
      in Thm.implies_intr (ctermF (jT inner23))
           (disjE_elimF (r2 xF, r3 xF, goalC) h caseR2 caseR3) end;
    val step123 =
      let val h = Thm.assume (ctermF (jT inner123))
      in Thm.implies_intr (ctermF (jT inner123))
           (disjE_elimF (r1 xF, inner23, goalC) h caseR1 step23) end;
    val concl = disjE_elimF (r0 xF, inner123, goalC) d4 caseR0 step123;
  in varify concl end;

(* odd_imp_r1_or_r3 : oddP x ==> Disj (r1 x)(r3 x)  from mod4_cases + odd_even_False *)
val odd_even_False_v = varify odd_even_False;
fun odd_even_False_at x hOdd hEven =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] odd_even_False_v)
  in Thm.implies_elim (Thm.implies_elim inst hOdd) hEven end;

val odd_imp_r1_or_r3 =
  let
    val xF = Free("x", natT);
    val hOdd = Thm.assume (ctermF (jT (oddP xF)));
    val d4 = mod4_cases_at xF;
    val goalC = mkDisj (r1 xF) (r3 xF);
    val caseR0 =
      let val h = Thm.assume (ctermF (jT (r0 xF)));
          val fls = odd_even_False_at xF hOdd (r0_even_at xF h);
      in Thm.implies_intr (ctermF (jT (r0 xF))) ((oFalse_elimF_at goalC) OF [fls]) end;
    val caseR1 =
      let val h = Thm.assume (ctermF (jT (r1 xF)))
      in Thm.implies_intr (ctermF (jT (r1 xF))) (disjI1F_at (r1 xF, r3 xF) h) end;
    val caseR2 =
      let val h = Thm.assume (ctermF (jT (r2 xF)));
          val fls = odd_even_False_at xF hOdd (r2_even_at xF h);
      in Thm.implies_intr (ctermF (jT (r2 xF))) ((oFalse_elimF_at goalC) OF [fls]) end;
    val caseR3 =
      let val h = Thm.assume (ctermF (jT (r3 xF)))
      in Thm.implies_intr (ctermF (jT (r3 xF))) (disjI2F_at (r1 xF, r3 xF) h) end;
    val inner23 = mkDisj (r2 xF) (r3 xF);
    val inner123 = mkDisj (r1 xF) inner23;
    val step23 =
      let val h = Thm.assume (ctermF (jT inner23))
      in Thm.implies_intr (ctermF (jT inner23))
           (disjE_elimF (r2 xF, r3 xF, goalC) h caseR2 caseR3) end;
    val step123 =
      let val h = Thm.assume (ctermF (jT inner123))
      in Thm.implies_intr (ctermF (jT inner123))
           (disjE_elimF (r1 xF, inner23, goalC) h caseR1 step23) end;
    val concl = disjE_elimF (r0 xF, inner123, goalC) d4 caseR0 step123;
    val disch = Thm.implies_intr (ctermF (jT (oddP xF))) concl;
  in varify disch end;

(* odd_mult_left : oddP (mult a b) ==> oddP a
     even_or_odd a -> case even a: even_mult -> even(ab); odd(ab)&even(ab)->False->odd a.
                      case odd a: done. *)
val even_mult_v = varify even_mult;
fun even_mult_at (a, b) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF a),(("b",0), ctermF b)] even_mult_v)) h;
val even_or_odd_v = varify even_or_odd;
fun even_or_odd_at x = beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] even_or_odd_v);

val odd_mult_left =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hOddAB = Thm.assume (ctermF (jT (oddP (mult aF bF))));
    val eo = even_or_odd_at aF;                   (* Disj (even a)(odd a) *)
    val goalC = oddP aF;
    val caseEven =
      let
        val hEvA = Thm.assume (ctermF (jT (evenP aF)));
        val hEvAB = even_mult_at (aF, bF) hEvA;   (* even(ab) *)
        val fls = odd_even_False_at (mult aF bF) hOddAB hEvAB;  (* oFalse *)
        val g = (oFalse_elimF_at goalC) OF [fls];
      in Thm.implies_intr (ctermF (jT (evenP aF))) g end;
    val caseOdd =
      let val h = Thm.assume (ctermF (jT (oddP aF)))
      in Thm.implies_intr (ctermF (jT (oddP aF))) h end;
    val concl = disjE_elimF (evenP aF, oddP aF, goalC) eo caseEven caseOdd;
    val disch = Thm.implies_intr (ctermF (jT (oddP (mult aF bF)))) concl;
  in varify disch end;

val xV6 = Var (("x",0), natT);
val aV6 = Var (("a",0), natT);
val bV6 = Var (("b",0), natT);
val r_eoo  = checkP ("even_or_odd", even_or_odd, jT (mkDisj (evenP xV6) (oddP xV6)));
val r_oir3 = checkP ("odd_imp_r1_or_r3", odd_imp_r1_or_r3,
    Logic.mk_implies (jT (oddP xV6), jT (mkDisj (r1 xV6) (r3 xV6))));
val r_oml  = checkP ("odd_mult_left", odd_mult_left,
    Logic.mk_implies (jT (oddP (mult aV6 bV6)), jT (oddP aV6)));

val () = if r_eoo andalso r_oir3 andalso r_oml then out "P3_PART6_OK\n" else out "P3_PART6_FAILED\n";
(* ============================================================================
   PART 7 : r1_mult  (r1 a ==> r1 b ==> r1 (mult a b))
   a = (4s)+1, b = (4t)+1.  Let A=4s, B=4t.
   ab = (A+1)(B+1) = ((A*B)+A) + (B+1)         [right_distrib + left_distrib + mult_1_left]
      = (((A*B)+A)+B) + 1                       [assoc]
   (A*B)+A+B = 4w  with w = (((s*B)+s)+t):
      A*B = 4*(s*B)   [A=4s, mult_assoc]
      (A*B)+A = 4*(s*B) + 4*s = 4*((s*B)+s)     [left_distrib backward]
      (..)+B   = 4*((s*B)+s) + 4*t = 4*(((s*B)+s)+t) = 4w
   ============================================================================ *)
val mult_1_left_v = varify mult_1_left;          (* oeq (mult (Suc 0) n) n *)
fun mult1l_atF t = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_1_left_v);
(* combine 4 multiples : add (mult 4 p)(mult 4 q) = mult 4 (add p q) *)
fun comb4 (p, q) = oeq_sym OF [left_distribF2_at (fourC, p, q)];

val r1_mult =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hA = Thm.assume (ctermF (jT (r1 aF)));
    val hB = Thm.assume (ctermF (jT (r1 bF)));
    val Pa = Abs("s", natT, oeq aF (add (mult fourC (Bound 0)) oneC));
    val Pb = Abs("t", natT, oeq bF (add (mult fourC (Bound 0)) oneC));
    val goalC = r1 (mult aF bF);
    fun bodyS s (hs : thm) =                      (* hs : a = (4s)+1 *)
      let
        fun bodyT t (ht : thm) =                  (* ht : b = (4t)+1 *)
          let
            val A = mult fourC s;   val B = mult fourC t;
            val aA1 = add A oneC;   val bB1 = add B oneC;
            (* ab = (A+1)*(B+1) via cong on both args *)
            val cl = mult_cong_lF (aF, aA1, bF) hs;     (* ab = (A+1)*b *)
            val cr = mult_cong_rF (aA1, bF, bB1) ht;    (* (A+1)*b = (A+1)*(B+1) *)
            val ab_prod = oeq_trans OF [cl, cr];        (* ab = (A+1)*(B+1) *)
            (* (A+1)*(B+1) = (A*(B+1)) + (1*(B+1))   right_distrib (m=A,n=1,k=(B+1)) *)
            val rd = rdistF_at (A, oneC, bB1);          (* mult (add A 1)(B+1) = add (mult A (B+1))(mult 1 (B+1)) *)
            (* mult A (B+1) = (A*B)+(A*1) = (A*B)+A   left_distrib + mult_1_right *)
            val ldA = left_distribF2_at (A, B, oneC);   (* A*(B+1) = (A*B)+(A*1) *)
            (* mult_1_right on ctxtF : A*1 = A *)
            val A1F = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF A)] (varify mult_1_right));
            val ldA2 = oeq_trans OF [ldA, add_cong_rF (mult A B, mult A oneC, A) A1F];  (* A*(B+1) = (A*B)+A *)
            (* 1*(B+1) = (B+1)  mult_1_left *)
            val m1 = mult1l_atF bB1;                    (* 1*(B+1) = (B+1) *)
            (* assemble : ab = ((A*B)+A) + (B+1) *)
            val rd2 = oeq_trans OF [rd,
                        oeq_trans OF [ add_cong_lF (mult A bB1, add (mult A B) A, mult oneC bB1) ldA2,
                                       add_cong_rF (add (mult A B) A, mult oneC bB1, bB1) m1 ]];
                                                        (* (A+1)(B+1) = ((A*B)+A)+(B+1) *)
            val ab1 = oeq_trans OF [ab_prod, rd2];      (* ab = ((A*B)+A)+(B+1) *)
            (* ((A*B)+A)+(B+1) = (((A*B)+A)+B)+1  assoc backward:
               add X (add B 1) = add (add X B) 1 with X=(A*B)+A *)
            val X = add (mult A B) A;
            val asc = oeq_sym OF [addassocF_at (X, B, oneC)];  (* ((A*B)+A)+(B+1) = (((A*B)+A)+B)+1 *)
            val ab2 = oeq_trans OF [ab1, asc];          (* ab = (((A*B)+A)+B)+1 *)
            (* now show (((A*B)+A)+B) = 4w *)
            (* A*B = 4*(s*B) : A=4s ; mult_assoc 4 s B *)
            val AB_assoc = multassocF_at (fourC, s, B);  (* (4*s)*B = 4*(s*B) *)
            (* (A*B)+A = 4*(s*B) + 4*s  then comb4 -> 4*((s*B)+s) *)
            (* first rewrite A*B -> 4*(s*B), and A -> 4*s (A = mult 4 s already) *)
            val cl_AB = add_cong_lF (mult A B, mult fourC (mult s B), A) AB_assoc;  (* (A*B)+A = (4*(s*B))+A *)
            (* A is literally mult fourC s, so (4*(s*B))+A = (4*(s*B))+(4*s) already *)
            val comb1 = comb4 (mult s B, s);            (* (4*(s*B))+(4*s) = 4*((s*B)+s) *)
            val XB1 = oeq_trans OF [cl_AB, comb1];      (* (A*B)+A = 4*((s*B)+s) *)
            (* (((A*B)+A)+B) = (4*((s*B)+s)) + (4*t)  [cong_l XB1; B = 4*t literally] *)
            val cl_X = add_cong_lF (X, mult fourC (add (mult s B) s), B) XB1;  (* X+B = (4*((s*B)+s))+B *)
            val comb2 = comb4 (add (mult s B) s, t);    (* (4*((s*B)+s))+(4*t) = 4*(((s*B)+s)+t) *)
            val XB_4w = oeq_trans OF [cl_X, comb2];     (* X+B = 4*w *)
            val w = add (add (mult s B) s) t;
            (* ab = (X+B)+1 = (4w)+1 *)
            val cl_final = add_cong_lF (add X B, mult fourC w, oneC) XB_4w;  (* (X+B)+1 = (4w)+1 *)
            val ab_form = oeq_trans OF [ab2, cl_final]; (* ab = (4w)+1 *)
          in r1_intro (mult aF bF, w) ab_form end;
        val g = exE_elimF (Pb, goalC) hB "t0" bodyT;
      in g end;
    val res = exE_elimF (Pa, goalC) hA "s0" bodyS;
    val d2 = Thm.implies_intr (ctermF (jT (r1 bF))) res;
    val d1 = Thm.implies_intr (ctermF (jT (r1 aF))) d2;
  in varify d1 end;

val aV7 = Var (("a",0), natT);
val bV7 = Var (("b",0), natT);
val r_r1_mult = checkP ("r1_mult", r1_mult,
    Logic.mk_implies (jT (r1 aV7), Logic.mk_implies (jT (r1 bV7), jT (r1 (mult aV7 bV7)))));

val () = if r_r1_mult then out "P3_PART7_OK\n" else out "P3_PART7_FAILED\n";
(* ============================================================================
   PART 8 : r1_r3_excl  (r1 x ==> r3 x ==> oFalse)
   ============================================================================ *)

(* add1_peel y : oeq (add y 1) (Suc y) *)
fun add1_peel y = oeq_sym OF [suc_as_add1_at y];   (* (add y 1) = Suc y *)
(* add3_peel y : oeq (add y 3) (Suc(Suc(Suc y)))
     add y (Suc(Suc(Suc 0))) = Suc(add y (Suc(Suc 0))) = Suc(Suc(add y (Suc 0)))
       = Suc(Suc(Suc(add y 0))) = Suc(Suc(Suc y))                                  *)
fun add3_peel y =
  let
    val p1 = addSrF_at (y, twoC);                 (* add y (Suc 2) = Suc(add y 2) *)  (* 3 = Suc 2 *)
    val p2 = addSrF_at (y, oneC);                 (* add y (Suc 1) = Suc(add y 1) *)  (* 2 = Suc 1 *)
    val p3 = addSrF_at (y, ZeroC);                (* add y (Suc 0) = Suc(add y 0) *)
    val p0 = add0rF_at y;                          (* add y 0 = y *)
    (* add y 1 = Suc y *)
    val a1 = oeq_trans OF [p3, Suc_cong OF [p0]];  (* add y 1 = Suc y *)
    (* add y 2 = Suc(add y 1) = Suc(Suc y) *)
    val a2 = oeq_trans OF [p2, Suc_cong OF [a1]];  (* add y 2 = Suc(Suc y) *)
    (* add y 3 = Suc(add y 2) = Suc(Suc(Suc y)) *)
    val a3 = oeq_trans OF [p1, Suc_cong OF [a2]];  (* add y 3 = Suc(Suc(Suc y)) *)
  in a3 end;

(* one_ne_4e3 : oeq 1 (add (4e) 3) ==> oFalse
     add(4e)3 = Suc(Suc(Suc(4e))) ; 1 = Suc 0 ; Suc 0 = Suc(Suc(Suc(4e))) -> Suc_inj
       -> 0 = Suc(Suc(4e)) -> sym -> Suc_neq_Zero.                              *)
val one_ne_4e3 =
  let
    val eF = Free("e", natT);
    val hyp = Thm.assume (ctermF (jT (oeq oneC (add (mult fourC eF) threeC))));
    val peel = add3_peel (mult fourC eF);          (* add(4e)3 = Suc(Suc(Suc(4e))) *)
    val one_S3 = oeq_trans OF [hyp, peel];          (* Suc 0 = Suc(Suc(Suc(4e))) *)   (* 1 = Suc 0 definitionally *)
    val inj1 = (Suc_inj_atF (ZeroC, suc (suc (mult fourC eF)))) OF [one_S3];  (* 0 = Suc(Suc(4e)) *)
    val sym1 = oeq_sym OF [inj1];                   (* Suc(Suc(4e)) = 0 *)
    val fls = (Suc_neq_ZeroF_at (suc (mult fourC eF))) OF [sym1];  (* oFalse *)
    val disch = Thm.implies_intr (ctermF (jT (oeq oneC (add (mult fourC eF) threeC)))) fls;
  in varify disch end;

(* two_ne_4e : oeq 2 (4e) ==> oFalse
     cases on e:
       e=0     : 4*0 = 0 ; 2 = 0 -> Suc(Suc 0) = 0 -> Suc_neq_Zero.
       e=Suc f : 4*(Suc f) = add 4 (4f) = Suc(Suc(Suc(Suc(4f)))) ;
                 2 = Suc(Suc 0) ; Suc(Suc 0) = Suc(Suc(Suc(Suc(4f)))) -> Suc_inj x2
                 -> 0 = Suc(Suc(4f)) -> sym -> Suc_neq_Zero.                       *)
(* add4_peel y : oeq (add 4 y) (Suc(Suc(Suc(Suc y))))   [add_Suc peels on the LEFT 4] *)
fun add4_peel y =
  let
    (* 4 = Suc 3 ; add (Suc 3) y = Suc(add 3 y) ; recurse to add 0 y = y *)
    val s1 = addSucF_at (threeC, y);              (* add 4 y = Suc(add 3 y) *)  (* 4 = Suc 3 *)
    val s2 = addSucF_at (twoC, y);                (* add 3 y = Suc(add 2 y) *)
    val s3 = addSucF_at (oneC, y);               (* add 2 y = Suc(add 1 y) *)
    val s4 = addSucF_at (ZeroC, y);              (* add 1 y = Suc(add 0 y) *)
    val s0 = add0F_at y;                          (* add 0 y = y *)
    val a1 = oeq_trans OF [s4, Suc_cong OF [s0]];          (* add 1 y = Suc y *)
    val a2 = oeq_trans OF [s3, Suc_cong OF [a1]];          (* add 2 y = Suc(Suc y) *)
    val a3 = oeq_trans OF [s2, Suc_cong OF [a2]];          (* add 3 y = Suc(Suc(Suc y)) *)
    val a4 = oeq_trans OF [s1, Suc_cong OF [a3]];          (* add 4 y = Suc(Suc(Suc(Suc y))) *)
  in a4 end;

val two_ne_4e =
  let
    val eF = Free("e", natT);
    val hyp = Thm.assume (ctermF (jT (oeq twoC (mult fourC eF))));   (* 2 = 4e *)
    val dz = dzosF_at eF;                          (* Disj (oeq e 0)(Ex q. oeq e (Suc q)) *)
    val caseZ =
      let
        val hz = Thm.assume (ctermF (jT (oeq eF ZeroC)));    (* e = 0 *)
        val cong = mult_cong_rF (fourC, eF, ZeroC) hz;        (* 4e = 4*0 *)
        val m40 = mult0rF_at fourC;                           (* 4*0 = 0 *)
        val e4_0 = oeq_trans OF [cong, m40];                  (* 4e = 0 *)
        val two_0 = oeq_trans OF [hyp, e4_0];                 (* 2 = 0 = Suc(Suc 0) = 0 *)
        (* 2 = Suc(Suc 0) ; so Suc(Suc 0) = 0 *)
        val sym2 = oeq_sym OF [two_0];                        (* 0 ... actually two_0 : Suc(Suc 0) = 0 *)
        val fls = (Suc_neq_ZeroF_at (suc ZeroC)) OF [two_0];  (* oFalse  (Suc(Suc 0) = 0) *)
      in Thm.implies_intr (ctermF (jT (oeq eF ZeroC))) fls end;
    val PsE = Abs("q", natT, oeq eF (suc (Bound 0)));
    val caseS =
      let
        val exq = Thm.assume (ctermF (jT (mkEx PsE)));
        fun sBody f (hf : thm) =                              (* e = Suc f *)
          let
            val cong = mult_cong_rF (fourC, eF, suc f) hf;     (* 4e = 4*(Suc f) *)
            val msr  = multSrF_at (fourC, f);                  (* 4*(Suc f) = add 4 (4f) *)
            val peel = add4_peel (mult fourC f);              (* add 4 (4f) = Suc(Suc(Suc(Suc(4f)))) *)
            val e4_S = oeq_trans OF [oeq_trans OF [cong, msr], peel];  (* 4e = Suc(Suc(Suc(Suc(4f)))) *)
            val two_S = oeq_trans OF [hyp, e4_S];             (* Suc(Suc 0) = Suc(Suc(Suc(Suc(4f)))) *)
            val inj1 = (Suc_inj_atF (suc ZeroC, suc(suc(suc(mult fourC f))))) OF [two_S];
                                                              (* Suc 0 = Suc(Suc(Suc(4f))) *)
            val inj2 = (Suc_inj_atF (ZeroC, suc(suc(mult fourC f)))) OF [inj1];
                                                              (* 0 = Suc(Suc(4f)) *)
            val sym2 = oeq_sym OF [inj2];                     (* Suc(Suc(4f)) = 0 *)
            val fls = (Suc_neq_ZeroF_at (suc (mult fourC f))) OF [sym2];  (* oFalse *)
          in fls end;
        val g = exE_elimF (PsE, oFalseC) exq "f0" sBody;
      in Thm.implies_intr (ctermF (jT (mkEx PsE))) g end;
    val concl = disjE_elimF (oeq eF ZeroC, mkEx PsE, oFalseC) dz caseZ caseS;
    val disch = Thm.implies_intr (ctermF (jT (oeq twoC (mult fourC eF)))) concl;
  in varify disch end;

val one_ne_4e3_v = varify one_ne_4e3;
val two_ne_4e_v  = varify two_ne_4e;
fun one_ne_4e3_at e h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("e",0), ctermF e)] one_ne_4e3_v)) h;
fun two_ne_4e_at  e h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("e",0), ctermF e)] two_ne_4e_v)) h;

(* r1_r3_excl : r1 x ==> r3 x ==> oFalse
   x = (4s)+1 = (4t)+3.  le_total s t:
     s<=t : t=s+e ; (4t)+3 = (4(s+e))+3 = ((4s)+(4e))+3 = (4s)+((4e)+3)
            (4s)+1 = (4s)+((4e)+3) -> cancel -> 1 = (4e)+3 -> one_ne_4e3.
     t<=s : s=t+e ; (4s)+1 = ((4t)+(4e))+1 = (4t)+((4e)+1)
            (4t)+((4e)+1) = (4t)+3 -> cancel -> (4e)+1 = 3 ; (4e)+1 = Suc(4e)
            Suc(4e) = 3 = Suc 2 -> Suc_inj -> 4e = 2 -> sym -> two_ne_4e. *)
val r1_r3_excl =
  let
    val xF = Free("x", natT);
    val hr1 = Thm.assume (ctermF (jT (r1 xF)));
    val hr3 = Thm.assume (ctermF (jT (r3 xF)));
    val P1 = Abs("s", natT, oeq xF (add (mult fourC (Bound 0)) oneC));
    val P3 = Abs("t", natT, oeq xF (add (mult fourC (Bound 0)) threeC));
    fun bodyS s (hs : thm) =                        (* x = (4s)+1 *)
      let
        fun bodyT t (ht : thm) =                    (* x = (4t)+3 *)
          let
            (* (4s)+1 = x = (4t)+3 *)
            val key = oeq_trans OF [oeq_sym OF [hs], ht];   (* (4s)+1 = (4t)+3 *)
            val dz = le_totalF_at (s, t);                   (* Disj (le s t)(le t s) *)
            val caseST =
              let
                val hle = Thm.assume (ctermF (jT (le s t)));
                val Pe = Abs("e", natT, oeq t (add s (Bound 0)));  (* le s t body *)
                fun eBody e (he : thm) =                 (* t = s+e *)
                  let
                    (* (4t) = 4*(s+e) = (4s)+(4e) *)
                    val c4t = mult_cong_rF (fourC, t, add s e) he;  (* 4t = 4*(s+e) *)
                    val ld  = left_distribF2_at (fourC, s, e);      (* 4*(s+e) = (4s)+(4e) *)
                    val t4_dist = oeq_trans OF [c4t, ld];           (* 4t = (4s)+(4e) *)
                    (* (4t)+3 = ((4s)+(4e))+3 = (4s)+((4e)+3) *)
                    val cl = add_cong_lF (mult fourC t, add (mult fourC s) (mult fourC e), threeC) t4_dist;
                    val asc = addassocF_at (mult fourC s, mult fourC e, threeC);
                    val rhs = oeq_trans OF [cl, asc];               (* (4t)+3 = (4s)+((4e)+3) *)
                    (* (4s)+1 = (4s)+((4e)+3) *)
                    val eqf = oeq_trans OF [key, rhs];              (* (4s)+1 = (4s)+((4e)+3) *)
                    val canc = add_left_cancelF OF [eqf];          (* 1 = (4e)+3 *)
                    val fls = one_ne_4e3_at e canc;
                  in fls end;
                val fls = exE_elimF (Pe, oFalseC) hle "e0" eBody;
              in Thm.implies_intr (ctermF (jT (le s t))) fls end;
            val caseTS =
              let
                val hle = Thm.assume (ctermF (jT (le t s)));
                val Pe = Abs("e", natT, oeq s (add t (Bound 0)));  (* le t s body *)
                fun eBody e (he : thm) =                 (* s = t+e *)
                  let
                    (* (4s) = 4*(t+e) = (4t)+(4e) *)
                    val c4s = mult_cong_rF (fourC, s, add t e) he;  (* 4s = 4*(t+e) *)
                    val ld  = left_distribF2_at (fourC, t, e);      (* 4*(t+e) = (4t)+(4e) *)
                    val s4_dist = oeq_trans OF [c4s, ld];           (* 4s = (4t)+(4e) *)
                    (* (4s)+1 = ((4t)+(4e))+1 = (4t)+((4e)+1) *)
                    val cl = add_cong_lF (mult fourC s, add (mult fourC t) (mult fourC e), oneC) s4_dist;
                    val asc = addassocF_at (mult fourC t, mult fourC e, oneC);
                    val lhs = oeq_trans OF [cl, asc];               (* (4s)+1 = (4t)+((4e)+1) *)
                    (* (4t)+((4e)+1) = (4s)+1 = (4t)+3 *)
                    val eqf = oeq_trans OF [oeq_sym OF [lhs], key]; (* (4t)+((4e)+1) = (4t)+3 *)
                    val canc = add_left_cancelF OF [eqf];          (* (4e)+1 = 3 *)
                    (* (4e)+1 = Suc(4e) ; 3 = Suc 2 ; Suc(4e) = Suc 2 -> Suc_inj -> 4e = 2 *)
                    val p1 = add1_peel (mult fourC e);             (* (4e)+1 = Suc(4e) *)
                    val S4e_3 = oeq_trans OF [oeq_sym OF [p1], canc];  (* Suc(4e) = 3 = Suc 2 *)
                    val inj = (Suc_inj_atF (mult fourC e, twoC)) OF [S4e_3];  (* 4e = 2 *)
                    val sym = oeq_sym OF [inj];                    (* 2 = 4e *)
                    val fls = two_ne_4e_at e sym;
                  in fls end;
                val fls = exE_elimF (Pe, oFalseC) hle "e0" eBody;
              in Thm.implies_intr (ctermF (jT (le t s))) fls end;
            val combined = disjE_elimF (le s t, le t s, oFalseC) dz caseST caseTS;
          in combined end;
        val g = exE_elimF (P3, oFalseC) hr3 "t0" bodyT;
      in g end;
    val res = exE_elimF (P1, oFalseC) hr1 "s0" bodyS;
    val d2 = Thm.implies_intr (ctermF (jT (r3 xF))) res;
    val d1 = Thm.implies_intr (ctermF (jT (r1 xF))) d2;
  in varify d1 end;

val xV8 = Var (("x",0), natT);
val r_excl = checkP ("r1_r3_excl", r1_r3_excl,
    Logic.mk_implies (jT (r1 xV8), Logic.mk_implies (jT (r3 xV8), jT oFalseC)));

val () = if r_excl then out "P3_PART8_OK\n" else out "P3_PART8_FAILED\n";
(* ============================================================================
   PART 9 : mul_r3_split  +  cofactor_bounds
   ============================================================================ *)
(* ex_middle + neg helpers on ctxtF *)
val ex_middle_vF = varify ex_middle_ax;
fun ex_middle_atF A = beta_norm (Drule.infer_instantiate ctxtF [(("A",0), ctermF A)] ex_middle_vF);
fun neg A = mkImp A oFalseC;
(* lift the residue/parity lemmas to ctxtF instantiators *)
val r3_imp_odd_vF = varify r3_imp_odd;
fun r3_odd_atF x h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r3_imp_odd_vF)) h;
val odd_mult_left_vF = varify odd_mult_left;
fun odd_mult_left_atF (a,b) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF a),(("b",0), ctermF b)] odd_mult_left_vF)) h;
val odd_imp_r1_or_r3_vF = varify odd_imp_r1_or_r3;
fun odd_imp_r1_or_r3_atF x h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] odd_imp_r1_or_r3_vF)) h;
val r1_mult_vF = varify r1_mult;
fun r1_mult_atF (a,b) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF a),(("b",0), ctermF b)] r1_mult_vF)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
val r1_r3_excl_vF = varify r1_r3_excl;
fun r1_r3_excl_atF x h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF [(("x",0), ctermF x)] r1_r3_excl_vF)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* multcomm subst : odd (mult a b) -> odd (mult b a)  via oeq_subst on mult_comm *)
fun odd_of_comm (a, b) hOddBA =        (* hOddBA : oddP (mult b a) -> produce oddP (mult a b) *)
  let
    val mc   = multcommF_at (b, a);                 (* (b*a) = (a*b) *)
    val zF   = Free("z_oc", natT);
    val Psub = Term.lambda zF (oddP zF);
    val subI = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Psub), (("a",0), ctermF (mult b a)), (("b",0), ctermF (mult a b))] oeq_subst_vF);
  in (subI OF [mc]) OF [hOddBA] end;

(* mul_r3_split : r3 (mult a b) ==> Disj (r3 a)(r3 b) *)
val mul_r3_split =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hr3ab = Thm.assume (ctermF (jT (r3 (mult aF bF))));
    val goalC = mkDisj (r3 aF) (r3 bF);
    (* odd(ab) -> odd a, odd b *)
    val oddAB = r3_odd_atF (mult aF bF) hr3ab;             (* oddP (mult a b) *)
    val oddA  = odd_mult_left_atF (aF, bF) oddAB;          (* oddP a *)
    (* odd b : odd(ba) from odd(ab) via comm-subst, then odd_mult_left *)
    val mc    = multcommF_at (aF, bF);                     (* (a*b) = (b*a) *)
    val oddBA =
      let
        val zF = Free("z_ba", natT);
        val Psub = Term.lambda zF (oddP zF);
        val subI = beta_norm (Drule.infer_instantiate ctxtF
              [(("P",0), ctermF Psub), (("a",0), ctermF (mult aF bF)), (("b",0), ctermF (mult bF aF))] oeq_subst_vF);
      in (subI OF [mc]) OF [oddAB] end;                    (* oddP (mult b a) *)
    val oddB  = odd_mult_left_atF (bF, aF) oddBA;          (* oddP b *)
    (* ex_middle on (r3 a) *)
    val emA = ex_middle_atF (r3 aF);                       (* Disj (r3 a)(neg(r3 a)) *)
    val caseR3a =
      let val h = Thm.assume (ctermF (jT (r3 aF)))
      in Thm.implies_intr (ctermF (jT (r3 aF))) (disjI1F_at (r3 aF, r3 bF) h) end;
    val caseNegR3a =
      let
        val hnegA = Thm.assume (ctermF (jT (neg (r3 aF))));    (* Imp (r3 a) oFalse *)
        (* ex_middle on (r3 b) *)
        val emB = ex_middle_atF (r3 bF);
        val caseR3b =
          let val h = Thm.assume (ctermF (jT (r3 bF)))
          in Thm.implies_intr (ctermF (jT (r3 bF))) (disjI2F_at (r3 aF, r3 bF) h) end;
        val caseNegR3b =
          let
            val hnegB = Thm.assume (ctermF (jT (neg (r3 bF))));  (* Imp (r3 b) oFalse *)
            (* odd a + ¬r3 a -> r1 a *)
            val d1a = odd_imp_r1_or_r3_atF aF oddA;             (* Disj (r1 a)(r3 a) *)
            val r1a =
              let
                val cR1 = let val h = Thm.assume (ctermF (jT (r1 aF)))
                          in Thm.implies_intr (ctermF (jT (r1 aF))) h end;
                val cR3 = let val h = Thm.assume (ctermF (jT (r3 aF)));
                              val fls = mp_atF (r3 aF, oFalseC) hnegA h;
                          in Thm.implies_intr (ctermF (jT (r3 aF))) ((oFalse_elimF_at (r1 aF)) OF [fls]) end;
              in disjE_elimF (r1 aF, r3 aF, r1 aF) d1a cR1 cR3 end;     (* r1 a *)
            val d1b = odd_imp_r1_or_r3_atF bF oddB;             (* Disj (r1 b)(r3 b) *)
            val r1b =
              let
                val cR1 = let val h = Thm.assume (ctermF (jT (r1 bF)))
                          in Thm.implies_intr (ctermF (jT (r1 bF))) h end;
                val cR3 = let val h = Thm.assume (ctermF (jT (r3 bF)));
                              val fls = mp_atF (r3 bF, oFalseC) hnegB h;
                          in Thm.implies_intr (ctermF (jT (r3 bF))) ((oFalse_elimF_at (r1 bF)) OF [fls]) end;
              in disjE_elimF (r1 bF, r3 bF, r1 bF) d1b cR1 cR3 end;     (* r1 b *)
            val r1ab = r1_mult_atF (aF, bF) r1a r1b;            (* r1 (mult a b) *)
            val fls = r1_r3_excl_atF (mult aF bF) r1ab hr3ab;   (* oFalse *)
            val g = (oFalse_elimF_at goalC) OF [fls];
          in Thm.implies_intr (ctermF (jT (neg (r3 bF)))) g end;
        val g = disjE_elimF (r3 bF, neg (r3 bF), goalC) emB caseR3b caseNegR3b;
      in Thm.implies_intr (ctermF (jT (neg (r3 aF)))) g end;
    val concl = disjE_elimF (r3 aF, neg (r3 aF), goalC) emA caseR3a caseNegR3a;
    val disch = Thm.implies_intr (ctermF (jT (r3 (mult aF bF)))) concl;
  in varify disch end;

val aV9 = Var (("a",0), natT);
val bV9 = Var (("b",0), natT);
val r_mrs = checkP ("mul_r3_split", mul_r3_split,
    Logic.mk_implies (jT (r3 (mult aV9 bV9)), jT (mkDisj (r3 aV9) (r3 bV9))));

val () = if r_mrs then out "P3_PART9_OK\n" else out "P3_PART9_FAILED\n";
(* ============================================================================
   PART 10 : cofactor_bounds
     lt 1 d ==> lt d n ==> oeq n (mult d e) ==> Conj (lt 1 e)(lt e n)
   ============================================================================ *)
val mult_1_right_vF = varify mult_1_right;
fun mult1r_atF t = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_1_right_vF);
(* le_intro already: le_introF ; lt 1 d = le 2 d = le (Suc(Suc 0)) d *)

(* helper: from lt 1 x (= le 2 x) extract x = Suc(Suc u), returning a thm via exE-cont. *)
fun lt1_destruct (xF, goalC) hlt1 contFn =
  let
    (* lt 1 x = le (Suc(Suc 0)) x = Ex u. oeq x (add (Suc(Suc 0)) u) *)
    val P = Abs("u", natT, oeq xF (add (suc (suc ZeroC)) (Bound 0)));
    fun body u (hu : thm) =                  (* hu : x = add 2 u *)
      let
        (* x = add 2 u = Suc(Suc u) : add (Suc(Suc 0)) u = Suc((Suc 0)+u) = Suc(Suc(0+u)) = Suc(Suc u) *)
        val a1 = addSucF_at (suc ZeroC, u);   (* (Suc(Suc 0))+u = Suc((Suc 0)+u) *)
        val a2 = addSucF_at (ZeroC, u);       (* (Suc 0)+u = Suc(0+u) *)
        val a0 = add0F_at u;                  (* 0+u = u *)
        val s2 = Suc_cong OF [oeq_trans OF [a2, Suc_cong OF [a0]]];  (* Suc((Suc 0)+u) = Suc(Suc u) *)
        val x_SSu = oeq_trans OF [hu, oeq_trans OF [a1, s2]];        (* x = Suc(Suc u) *)
      in contFn u x_SSu end;
  in exE_elimF (P, goalC) hlt1 "u_d" body end;

val cofactor_bounds =
  let
    val dF = Free("d", natT); val nF = Free("n", natT); val eF = Free("e", natT);
    val h1dP = jT (ltF (suc ZeroC) dF);     (* lt 1 d *)
    val hdnP = jT (ltF dF nF);              (* lt d n *)
    val hneP = jT (oeq nF (mult dF eF));    (* n = d*e *)
    val h1d  = Thm.assume (ctermF h1dP);
    val hdn  = Thm.assume (ctermF hdnP);
    val hne  = Thm.assume (ctermF hneP);
    val goalC = mkConj (ltF (suc ZeroC) eF) (ltF eF nF);

    (* ===== 1 < e ===== *)
    (* dz on e: e=0 or e=Suc q *)
    val dze = dzosF_at eF;
    val lt1e =
      let
        val caseZ =
          let
            val hz = Thm.assume (ctermF (jT (oeq eF ZeroC)));   (* e = 0 *)
            (* n = d*e = d*0 = 0 *)
            val cong = mult_cong_rF (dF, eF, ZeroC) hz;          (* d*e = d*0 *)
            val m0   = mult0rF_at dF;                            (* d*0 = 0 *)
            val n_0  = oeq_trans OF [oeq_trans OF [hne, cong], m0]; (* n = 0 *)
            (* lt d n = le (Suc d) n ; n=0 -> le (Suc d) 0 -> exE w : 0 = Suc d + w -> Suc_neq *)
            (* subst n->0 in (le (Suc d) _) : P z := le (Suc d) z *)
            val zF = Free("z_cz", natT);
            val Psub = Term.lambda zF (le (suc dF) zF);
            val subI = beta_norm (Drule.infer_instantiate ctxtF
                  [(("P",0), ctermF Psub), (("a",0), ctermF nF), (("b",0), ctermF ZeroC)] oeq_subst_vF);
            val leSd0 = (subI OF [n_0]) OF [hdn];                (* le (Suc d) 0 *)
            (* exE: 0 = add (Suc d) w -> Suc(...) = 0 -> Suc_neq *)
            val Pw = Abs("w", natT, oeq ZeroC (add (suc dF) (Bound 0)));
            fun wBody w (hw : thm) =                             (* 0 = add (Suc d) w *)
              let
                val aS = addSucF_at (dF, w);                     (* (Suc d)+w = Suc(d+w) *)
                val z_S = oeq_trans OF [hw, aS];                 (* 0 = Suc(d+w) *)
                val S_z = oeq_sym OF [z_S];
              in (Suc_neq_ZeroF_at (add dF w)) OF [S_z] end;
            val fls = exE_elimF (Pw, oFalseC) leSd0 "w0" wBody;
            val g = (oFalse_elimF_at (ltF (suc ZeroC) eF)) OF [fls];
          in Thm.implies_intr (ctermF (jT (oeq eF ZeroC))) g end;
        val PsE = Abs("q", natT, oeq eF (suc (Bound 0)));
        val caseS =
          let
            val exq = Thm.assume (ctermF (jT (mkEx PsE)));
            fun sBody q (hq : thm) =                             (* e = Suc q *)
              let
                (* sub-case q = 0 -> e = 1 -> n = d*1 = d -> lt d d -> lt_irrefl ;
                   q = Suc r -> e = Suc(Suc r) -> 1 < e directly. *)
                val dzq = dzosF_at q;
                val caseQZ =
                  let
                    val hqz = Thm.assume (ctermF (jT (oeq q ZeroC)));   (* q = 0 *)
                    (* e = Suc q = Suc 0 = 1 *)
                    val e_1 = oeq_trans OF [hq, Suc_cong OF [hqz]];      (* e = Suc 0 = 1 *)
                    (* n = d*e = d*1 = d *)
                    val cong = mult_cong_rF (dF, eF, oneC) e_1;          (* d*e = d*1 *)
                    val m1   = mult1r_atF dF;                            (* d*1 = d *)
                    val n_d  = oeq_trans OF [oeq_trans OF [hne, cong], m1]; (* n = d *)
                    (* lt d n ; subst n->d : lt d d ; lt_irrefl *)
                    val zF = Free("z_qz", natT);
                    val Psub = Term.lambda zF (ltF dF zF);              (* %z. le (Suc d) z *)
                    val subI = beta_norm (Drule.infer_instantiate ctxtF
                          [(("P",0), ctermF Psub), (("a",0), ctermF nF), (("b",0), ctermF dF)] oeq_subst_vF);
                    val ltdd = (subI OF [n_d]) OF [hdn];                (* lt d d *)
                    val fls  = lt_irreflF_at dF ltdd;                  (* oFalse *)
                    val g = (oFalse_elimF_at (ltF (suc ZeroC) eF)) OF [fls];
                  in Thm.implies_intr (ctermF (jT (oeq q ZeroC))) g end;
                val PsQ = Abs("r", natT, oeq q (suc (Bound 0)));
                val caseQS =
                  let
                    val exr = Thm.assume (ctermF (jT (mkEx PsQ)));
                    fun rBody r (hr : thm) =                            (* q = Suc r *)
                      let
                        (* e = Suc q = Suc(Suc r) ; 1 < e = le 2 e ; witness r :
                           e = Suc(Suc r) = add 2 r ?  add (Suc(Suc 0)) r = Suc(Suc r). *)
                        val e_SSr = oeq_trans OF [hq, Suc_cong OF [hr]];   (* e = Suc(Suc r) *)
                        (* Suc(Suc r) = add 2 r *)
                        val a1 = addSucF_at (suc ZeroC, r); val a2 = addSucF_at (ZeroC, r); val a0 = add0F_at r;
                        val a2r = oeq_trans OF [a1, Suc_cong OF [oeq_trans OF [a2, Suc_cong OF [a0]]]];
                                                                        (* add 2 r = Suc(Suc r) *)
                        val SSr_add = oeq_sym OF [a2r];                 (* Suc(Suc r) = add 2 r *)
                        val e_2r = oeq_trans OF [e_SSr, SSr_add];       (* e = add 2 r *)
                        val le2e = le_introF (suc (suc ZeroC), eF, r) e_2r;  (* le 2 e = lt 1 e *)
                      in le2e end;
                    val g = exE_elimF (PsQ, ltF (suc ZeroC) eF) exr "r0" rBody;
                  in Thm.implies_intr (ctermF (jT (mkEx PsQ))) g end;
                val combined = disjE_elimF (oeq q ZeroC, mkEx PsQ, ltF (suc ZeroC) eF) dzq caseQZ caseQS;
              in combined end;
            val g = exE_elimF (PsE, ltF (suc ZeroC) eF) exq "q0" sBody;
          in Thm.implies_intr (ctermF (jT (mkEx PsE))) g end;
        val combined = disjE_elimF (oeq eF ZeroC, mkEx PsE, ltF (suc ZeroC) eF) dze caseZ caseS;
      in combined end;   (* lt1e : jT (lt 1 e) *)

    (* ===== e < n ===== *)
    (* From lt1e get e = Suc(Suc e0).  d = Suc(Suc u) (lt1_destruct on h1d).
       n = d*e = (Suc(Suc u))*e = add e (mult (Suc u) e).
       Y := mult (Suc u) e = add e (mult u e) ; Y = mult(Suc u) e ; multSuc.
       n = add e Y.  e = Suc(Suc e0) -> n = add (Suc(Suc e0)) Y = Suc(Suc(add e0 Y)).
       le (Suc e) n : witness Y_pred? simpler: n = add e Y, Y >= 1 (Y = mult(Suc u)e, e>=2>0).
       Use:  n = add e Y ; le (Suc e) n  <=>  exists p. n = add (Suc e) p.
       Y = mult (Suc u) e = add e (mult u e).  So n = add e (add e (mult u e))
                                                  = add (add e e)(mult u e) (assoc backward? )
       Cleaner: n = add e Y.  e = Suc e0' (from lt1e, e = Suc(Suc e0)).
         Actually need le (Suc e) n.  n = add e Y.  Want add (Suc e) p = add e Y.
         add (Suc e) p = Suc(add e p) ; add e Y with Y = Suc Y0 -> add e (Suc Y0) = Suc(add e Y0).
         So p := Y0 with Y = Suc Y0.  Need Y = Suc Y0, i.e. Y >= 1.
         Y = mult (Suc u) e = add e (mult u e) ; e = Suc(Suc e0) -> Y = add (Suc(Suc e0))(mult u e)
            = Suc(Suc(add e0 (mult u e))) -> Y0 = Suc(add e0 (mult u e)). *)
    val ltn =
      let
        fun afterE0E u hd_SSu =        (* hd_SSu : d = Suc(Suc u) *)
          let
            (* destruct e = Suc(Suc e0) from lt1e *)
            val P = Abs("e0", natT, oeq eF (add (suc (suc ZeroC)) (Bound 0)));
            fun eBody e0 (he0 : thm) =                  (* he0 : e = add 2 e0 *)
              let
                (* e = Suc(Suc e0) *)
                val a1 = addSucF_at (suc ZeroC, e0); val a2 = addSucF_at (ZeroC, e0); val a0 = add0F_at e0;
                val e_SSe0 = oeq_trans OF [he0, oeq_trans OF [a1, Suc_cong OF [oeq_trans OF [a2, Suc_cong OF [a0]]]]];
                                                        (* e = Suc(Suc e0) *)
                (* n = d*e ; d = Suc(Suc u) -> d*e = (Suc(Suc u))*e = add e (mult (Suc u) e) *)
                val cong = mult_cong_lF (dF, suc (suc u), eF) hd_SSu;  (* d*e = (Suc(Suc u))*e *)
                val mS   = multSucF_at (suc u, eF);                    (* (Suc(Suc u))*e = add e (mult (Suc u) e) *)
                val n_eY = oeq_trans OF [oeq_trans OF [hne, cong], mS];  (* n = add e (mult (Suc u) e) *)
                val Y = mult (suc u) eF;
                (* Y = add e (mult u e) [multSuc] ; e=Suc(Suc e0) -> Y = Suc(Suc(add e0 (mult u e))) *)
                val mSY = multSucF_at (u, eF);          (* (Suc u)*e = add e (mult u e) *)
                (* add e (mult u e) with e = Suc(Suc e0):
                   add (Suc(Suc e0)) Z = Suc(add (Suc e0) Z) = Suc(Suc(add e0 Z)) *)
                val Z = mult u eF;
                val cle = add_cong_lF (eF, suc (suc e0), Z) e_SSe0;  (* add e Z = add (Suc(Suc e0)) Z *)
                val pe1 = addSucF_at (suc e0, Z);        (* add (Suc(Suc e0)) Z = Suc(add (Suc e0) Z) *)
                val pe2 = addSucF_at (e0, Z);            (* add (Suc e0) Z = Suc(add e0 Z) *)
                val Y_eZ = oeq_trans OF [mSY, cle];      (* Y = add (Suc(Suc e0)) Z *)
                val Y_SS = oeq_trans OF [Y_eZ, oeq_trans OF [pe1, Suc_cong OF [pe2]]];  (* Y = Suc(Suc(add e0 Z)) *)
                (* so Y = Suc Y0 with Y0 = Suc(add e0 Z) *)
                val Y0 = suc (add e0 Z);
                (* n = add e Y = add e (Suc Y0) [cong on Y] = Suc(add e Y0) = add (Suc e) ...
                   We want le (Suc e) n witness Y0 : n = add (Suc e) Y0.
                   add (Suc e) Y0 = Suc(add e Y0).  n = add e Y = add e (Suc Y0) = Suc(add e Y0). *)
                val congY = add_cong_rF (eF, Y, suc Y0) Y_SS;     (* add e Y = add e (Suc Y0) *)
                val n_eSY0 = oeq_trans OF [n_eY, congY];          (* n = add e (Suc Y0) *)
                val aSr = addSrF_at (eF, Y0);                     (* add e (Suc Y0) = Suc(add e Y0) *)
                val n_SeY0 = oeq_trans OF [n_eSY0, aSr];          (* n = Suc(add e Y0) *)
                val aSl = addSucF_at (eF, Y0);                    (* add (Suc e) Y0 = Suc(add e Y0) *)
                val n_Se = oeq_trans OF [n_SeY0, oeq_sym OF [aSl]]; (* n = add (Suc e) Y0 *)
                val le_Se_n = le_introF (suc eF, nF, Y0) n_Se;    (* le (Suc e) n = lt e n *)
              in le_Se_n end;
            val g = exE_elimF (P, ltF eF nF) lt1e "e0_w" eBody;
          in g end;
        val g = lt1_destruct (dF, ltF eF nF) h1d afterE0E;
      in g end;   (* ltn : jT (lt e n) *)

    val conj = conjI_atF (ltF (suc ZeroC) eF, ltF eF nF) lt1e ltn;
    val d3 = Thm.implies_intr (ctermF hneP) conj;
    val d2 = Thm.implies_intr (ctermF hdnP) d3;
    val d1 = Thm.implies_intr (ctermF h1dP) d2;
  in varify d1 end;

val dV10 = Var (("d",0), natT);
val nV10 = Var (("n",0), natT);
val eV10 = Var (("e",0), natT);
val cofactor_bounds_intended =
  Logic.mk_implies (jT (ltF (suc ZeroC) dV10),
    Logic.mk_implies (jT (ltF dV10 nV10),
      Logic.mk_implies (jT (oeq nV10 (mult dV10 eV10)),
        jT (mkConj (ltF (suc ZeroC) eV10) (ltF eV10 nV10)))));
val r_cofb = checkP ("cofactor_bounds", cofactor_bounds, cofactor_bounds_intended);

val () = if r_cofb then out "P3_PART10_OK\n" else out "P3_PART10_FAILED\n";
(* ============================================================================
   PART 11 : THE KEY LEMMA
     prime_factor_3mod4 :
       jT (r3 m) ==> jT (lt (Suc Zero) m)
         ==> jT (Ex (%q. Conj (Conj (prime2 q)(dvd q m)) (r3 q)))
   by strong_induct on m.
   ============================================================================ *)
val () = out "P3_KEY_BEGIN\n";

(* strong_induct lifted to ctxtF *)
val strong_induct_vF = varify strong_induct;
(* prime_cases lifted to ctxtF *)
val prime_cases_vF = varify prime_cases;
fun prime_cases_atF nt hgt1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF nt)] prime_cases_vF)
  in Thm.implies_elim inst hgt1 end;
(* dvd_refl lifted to ctxtF *)
val dvd_refl_vF = varify dvd_refl;
fun dvd_refl_atF t = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF t)] dvd_refl_vF);
(* mul_r3_split lifted to ctxtF *)
val mul_r3_split_vF = varify mul_r3_split;
fun mul_r3_split_atF (a,b) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF a),(("b",0), ctermF b)] mul_r3_split_vF)) h;
(* cofactor_bounds lifted to ctxtF *)
val cofactor_bounds_vF = varify cofactor_bounds;
fun cofactor_bounds_atF (d,n,e) h1 h2 h3 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("d",0), ctermF d),(("n",0), ctermF n),(("e",0), ctermF e)] cofactor_bounds_vF)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst h1) h2) h3 end;

(* allI/forall_elim helpers : strong_induct hyp is a meta !! form, handled directly. *)

(* the result existential body (capture-avoiding) :
     %q. Conj (Conj (prime2 q)(dvd q n)) (r3 q) *)
fun keyBodyAbs nt =
  let val qF = Free("q_kb", natT)
  in Term.lambda qF (mkConj (mkConj (prime2 qF) (dvd qF nt)) (r3 qF)) end;
fun keyEx nt = mkEx (keyBodyAbs nt);
(* the strong-induct predicate body : Imp (r3 n)(Imp (lt 1 n)(keyEx n)) *)
fun Pbody nt = mkImp (r3 nt) (mkImp (ltF (suc ZeroC) nt) (keyEx nt));

val prime_factor_3mod4 =
  let
    (* ---- the step : fix n, given strong IH, prove jT (Pbody n) ---- *)
    val nStep = Free("n_step", natT);
    val mIH   = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (ltF mIH nStep), jT (Pbody mIH)));
    val Hthm  = Thm.assume (ctermF Gprop);
    fun applyIH dt h_lt =                       (* h_lt : jT (lt d n) -> jT (Pbody d) *)
      let val hAt = Thm.forall_elim (ctermF dt) Hthm
      in Thm.implies_elim hAt h_lt end;

    (* assume r3 n and lt 1 n *)
    val hr3n_P = jT (r3 nStep);
    val h1n_P  = jT (ltF (suc ZeroC) nStep);
    val hr3n   = Thm.assume (ctermF hr3n_P);
    val h1n    = Thm.assume (ctermF h1n_P);
    val goalC  = keyEx nStep;

    (* prime_cases at n -> Disj (prime2 n)(Ex d. Conj(Conj(1<d)(d<n))(d|n)) *)
    val pd_Abs =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (mkConj (ltF (suc ZeroC) dF) (ltF dF nStep)) (dvd dF nStep)) end;
    val pdEx = mkEx pd_Abs;
    val dThm = prime_cases_atF nStep h1n;        (* Disj (prime2 n) pdEx *)

    (* CASE A : prime2 n -> q := n *)
    val caseA =
      let
        val hp  = Thm.assume (ctermF (jT (prime2 nStep)));
        val dnn = dvd_refl_atF nStep;            (* dvd n n *)
        val cInner = conjI_atF (prime2 nStep, dvd nStep nStep) hp dnn;   (* Conj(prime2 n)(dvd n n) *)
        val cFull  = conjI_atF (mkConj (prime2 nStep) (dvd nStep nStep), r3 nStep) cInner hr3n;
                                                  (* Conj(Conj(prime2 n)(dvd n n))(r3 n) *)
        val ex = exI_atF (keyBodyAbs nStep) nStep cFull;   (* keyEx n *)
      in Thm.implies_intr (ctermF (jT (prime2 nStep))) ex end;

    (* CASE B : pdEx -> exE witness d (1<d, d<n, d|n) *)
    val caseB =
      let
        val hpd = Thm.assume (ctermF (jT pdEx));
        fun pdBody d (hConj : thm) =             (* hConj : Conj(Conj(1<d)(d<n))(d|n) *)
          let
            val innerC = mkConj (ltF (suc ZeroC) d) (ltF d nStep);
            val hInner = conjunct1_atF (innerC, dvd d nStep) hConj;   (* Conj(1<d)(d<n) *)
            val hDvdDN = conjunct2_atF (innerC, dvd d nStep) hConj;   (* dvd d n *)
            val h_1lt_d= conjunct1_atF (ltF (suc ZeroC) d, ltF d nStep) hInner;  (* 1<d *)
            val h_lt_dn= conjunct2_atF (ltF (suc ZeroC) d, ltF d nStep) hInner;  (* d<n *)
            (* cofactor e : exE on dvd d n -> e with n = d*e *)
            val Pdvd = Abs("k", natT, oeq nStep (mult d (Bound 0)));   (* dvd d n body *)
            fun eBody e (hne : thm) =             (* hne : oeq n (mult d e) *)
              let
                (* bounds on e *)
                val cofb = cofactor_bounds_atF (d, nStep, e) h_1lt_d h_lt_dn hne;  (* Conj(1<e)(e<n) *)
                val h_1lt_e = conjunct1_atF (ltF (suc ZeroC) e, ltF e nStep) cofb;
                val h_lt_en = conjunct2_atF (ltF (suc ZeroC) e, ltF e nStep) cofb;
                (* r3 n = r3 (d*e) via subst n -> d*e ;  hr3n : r3 n *)
                val zF = Free("z_r3", natT);
                val Psub = Term.lambda zF (r3 zF);
                val subI = beta_norm (Drule.infer_instantiate ctxtF
                      [(("P",0), ctermF Psub), (("a",0), ctermF nStep), (("b",0), ctermF (mult d e))] oeq_subst_vF);
                val hr3de = (subI OF [hne]) OF [hr3n];      (* r3 (mult d e) *)
                val split = mul_r3_split_atF (d, e) hr3de;  (* Disj (r3 d)(r3 e) *)
                (* CASE r3 d : IH at d *)
                val caseR3d =
                  let
                    val hr3d = Thm.assume (ctermF (jT (r3 d)));
                    val Pd = applyIH d h_lt_dn;             (* jT (Pbody d) = Imp(r3 d)(Imp(1<d)(keyEx d)) *)
                    val step1 = mp_atF (r3 d, mkImp (ltF (suc ZeroC) d) (keyEx d)) Pd hr3d;  (* Imp(1<d)(keyEx d) *)
                    val exd = mp_atF (ltF (suc ZeroC) d, keyEx d) step1 h_1lt_d;             (* keyEx d *)
                    (* exE on keyEx d : witness q with Conj(Conj(prime2 q)(dvd q d))(r3 q) *)
                    fun qBody q (hq : thm) =
                      let
                        val hInQ = conjunct1_atF (mkConj (prime2 q) (dvd q d), r3 q) hq;  (* Conj(prime2 q)(dvd q d) *)
                        val hr3q = conjunct2_atF (mkConj (prime2 q) (dvd q d), r3 q) hq;  (* r3 q *)
                        val hPrime = conjunct1_atF (prime2 q, dvd q d) hInQ;             (* prime2 q *)
                        val hDvdQD = conjunct2_atF (prime2 q, dvd q d) hInQ;             (* dvd q d *)
                        val hDvdQN = dvd_trans_atF (q, d, nStep) hDvdQD hDvdDN;          (* dvd q n *)
                        val cIn  = conjI_atF (prime2 q, dvd q nStep) hPrime hDvdQN;
                        val cAll = conjI_atF (mkConj (prime2 q) (dvd q nStep), r3 q) cIn hr3q;
                      in exI_atF (keyBodyAbs nStep) q cAll end;
                    val g = exE_elimF (keyBodyAbs d, goalC) exd "q_d" qBody;
                  in Thm.implies_intr (ctermF (jT (r3 d))) g end;
                (* CASE r3 e : IH at e (needs 1<e, e<n) *)
                val caseR3e =
                  let
                    val hr3e = Thm.assume (ctermF (jT (r3 e)));
                    val Pe = applyIH e h_lt_en;             (* jT (Pbody e) *)
                    val step1 = mp_atF (r3 e, mkImp (ltF (suc ZeroC) e) (keyEx e)) Pe hr3e;
                    val exe = mp_atF (ltF (suc ZeroC) e, keyEx e) step1 h_1lt_e;   (* keyEx e *)
                    (* dvd e n : n = d*e = e*d -> e | n ; witness d, body oeq n (mult e d) *)
                    val mc = multcommF_at (d, e);          (* (d*e) = (e*d) *)
                    val n_ed = oeq_trans OF [hne, mc];     (* n = (e*d) *)
                    val dvdEN = dvd_introF (e, nStep, d) n_ed;   (* dvd e n *)
                    fun qBody q (hq : thm) =
                      let
                        val hInQ = conjunct1_atF (mkConj (prime2 q) (dvd q e), r3 q) hq;
                        val hr3q = conjunct2_atF (mkConj (prime2 q) (dvd q e), r3 q) hq;
                        val hPrime = conjunct1_atF (prime2 q, dvd q e) hInQ;
                        val hDvdQE = conjunct2_atF (prime2 q, dvd q e) hInQ;
                        val hDvdQN = dvd_trans_atF (q, e, nStep) hDvdQE dvdEN;   (* dvd q n *)
                        val cIn  = conjI_atF (prime2 q, dvd q nStep) hPrime hDvdQN;
                        val cAll = conjI_atF (mkConj (prime2 q) (dvd q nStep), r3 q) cIn hr3q;
                      in exI_atF (keyBodyAbs nStep) q cAll end;
                    val g = exE_elimF (keyBodyAbs e, goalC) exe "q_e" qBody;
                  in Thm.implies_intr (ctermF (jT (r3 e))) g end;
                val combined = disjE_elimF (r3 d, r3 e, goalC) split caseR3d caseR3e;
              in combined end;
            val g = exE_elimF (Pdvd, goalC) hDvdDN "e_w" eBody;
          in g end;
        val g = exE_elimF (pd_Abs, goalC) hpd "d_w" pdBody;
      in Thm.implies_intr (ctermF (jT pdEx)) g end;

    val concl = disjE_elimF (prime2 nStep, pdEx, goalC) dThm caseA caseB;   (* keyEx n *)
    (* build Pbody n = Imp (r3 n)(Imp (lt 1 n)(keyEx n)) *)
    val inner = impI_atF (ltF (suc ZeroC) nStep, keyEx nStep)
                  (Thm.implies_intr (ctermF h1n_P) concl);    (* Imp (lt 1 n)(keyEx n) *)
    val Pn = impI_atF (r3 nStep, mkImp (ltF (suc ZeroC) nStep) (keyEx nStep))
                  (Thm.implies_intr (ctermF hr3n_P) inner);   (* Pbody n *)
    val stepThm = Thm.forall_intr (ctermF nStep) (Thm.implies_intr (ctermF Gprop) Pn);

    (* feed to strong_induct : P := %n. Pbody n *)
    val mPred =
      let val nF = Free("n_pred", natT)
      in Term.lambda nF (Pbody nF) end;
    val kF = Free("m", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtF
                   [(("P",0), ctermF mPred), (("k",0), ctermF kF)] strong_induct_vF);
    val Pk = Thm.implies_elim siInst stepThm;        (* jT (Pbody m) *)
    (* turn into the implication form : r3 m ==> lt 1 m ==> keyEx m *)
    val hr3m = Thm.assume (ctermF (jT (r3 kF)));
    val h1m  = Thm.assume (ctermF (jT (ltF (suc ZeroC) kF)));
    val s1   = mp_atF (r3 kF, mkImp (ltF (suc ZeroC) kF) (keyEx kF)) Pk hr3m;
    val exM  = mp_atF (ltF (suc ZeroC) kF, keyEx kF) s1 h1m;     (* keyEx m *)
    val d2   = Thm.implies_intr (ctermF (jT (ltF (suc ZeroC) kF))) exM;
    val d1   = Thm.implies_intr (ctermF (jT (r3 kF))) d2;
  in varify d1 end;

(* ---- validation ---- *)
val mVk = Var (("m",0), natT);
val key_intended =
  let
    val qF = Free("q_kb", natT)
    val bodyAbs = Term.lambda qF (mkConj (mkConj (prime2 qF) (dvd qF mVk)) (r3 qF))
  in Logic.mk_implies (jT (r3 mVk),
       Logic.mk_implies (jT (ltF (suc ZeroC) mVk), jT (mkEx bodyAbs))) end;
val r_key = checkP ("prime_factor_3mod4", prime_factor_3mod4, key_intended);

(* SOUNDNESS PROBES : kernel must reject false variants *)
val probe_key_prime =
  let val qF = Free("q_kb", natT)
      val bogusAbs = Term.lambda qF (mkConj (dvd qF mVk) (r3 qF))   (* drops prime2 *)
      val bogus = Logic.mk_implies (jT (r3 mVk), Logic.mk_implies (jT (ltF (suc ZeroC) mVk), jT (mkEx bogusAbs)))
  in not ((Thm.prop_of prime_factor_3mod4) aconv bogus) end;
val probe_key_r3 =
  let val qF = Free("q_kb", natT)
      val bogusAbs = Term.lambda qF (mkConj (prime2 qF) (dvd qF mVk))  (* drops r3 q *)
      val bogus = Logic.mk_implies (jT (r3 mVk), Logic.mk_implies (jT (ltF (suc ZeroC) mVk), jT (mkEx bogusAbs)))
  in not ((Thm.prop_of prime_factor_3mod4) aconv bogus) end;

val () = if probe_key_prime andalso probe_key_r3
         then out "P3_KEY_PROBE_OK\n" else out "P3_KEY_PROBE_UNSOUND\n";
val () = if r_key andalso probe_key_prime andalso probe_key_r3
         then out "P3_KEY_DONE\n" else out "P3_KEY_FAILED\n";
val () = if r_key then out "BASE_OK\n" else out "BASE_FAILED\n";
(* ============================================================================
   THE FINALE (direct):  infinitely many primes  ==  3 (mod 4)
     P3MOD4_ALL : |- Forall (%n. Ex (%q. Conj (prime2 q) (Conj (lt n q) (r3 q))))
   i.e.  forall n. exists q. prime2 q  /\  n < q  /\  q = 3 (mod 4).
   ----------------------------------------------------------------------------
   Built on the foundation delta (/tmp/p3_base_delta.sml): the KEY LEMMA
     prime_factor_3mod4 : r3 m ==> 1<m ==> Ex q. (prime2 q /\ q|m) /\ r3 q
   and the Euclid helpers (fact, fact_pos, dvd_fact, consec_coprime) on ctxtF.

   PROOF (Euclid-style, additive mod-4, NO subtraction):
     fix Free n.  fact_pos gives n! >= 1, so n! = Suc P for some P (= n!-1).
     Let N = (4*P) + 3.   Then:
       - r3 N         immediate (r3_intro, witness P).
       - 1 < N        N = Suc(Suc(Suc(4P))) >= 2 > 1.
       - Suc N = 4*(n!) :  Suc((4P)+3) = (4P)+4 = 4*(Suc P) = 4*(n!).
     prime_factor_3mod4 at N  ->  Ex q. (prime2 q /\ q|N) /\ r3 q.   exE q.
     CLAIM  n < q :  le_total (Suc n, q) -> Disj (lt n q)(le q (Suc n)).
       Case lt n q : direct.
       Case le q (Suc n) : le_cases (q, n) -> Disj (le q n)(oeq q (Suc n)).
         Sub le q n :  le 1 q (from prime2's 1<q via le_trans le_one_two);
                       dvd_fact (le 1 q)(le q n) -> q | n!.
                       dvd_mult_right -> q | (n! * 4) ; mult_comm -> q | (4*n!) = Suc N.
                       consec_coprime (1<q)(q|N)(q|Suc N) -> oFalse -> lt n q.
         Sub oeq q (Suc n) : lt n q = le (Suc n) q ; q = Suc n ; le_refl + subst.
     Conj (prime2 q)(Conj (lt n q)(r3 q)) ; exI ; allI over n.
   ============================================================================ *)
val () = out "P3FIN_BEGIN\n";

(* ---- lift the pieces we still need onto ctxtF ---- *)
val dvd_mult_right_vF = varify dvd_mult_right;
fun dvd_mult_right_atF (a,b,c) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("a",0), ctermF a),(("b",0), ctermF b),(("c",0), ctermF c)] dvd_mult_right_vF)
  in Thm.implies_elim inst h end;

(* prime_factor_3mod4 lifted to ctxtF *)
val prime_factor_3mod4_vF = varify prime_factor_3mod4;
fun prime_factor_3mod4_atF mt hr3 h1lt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF [(("m",0), ctermF mt)] prime_factor_3mod4_vF)
  in Thm.implies_elim (Thm.implies_elim inst hr3) h1lt end;

(* ---- the RESULT existential body (capture-avoiding via Term.lambda over a Free):
        %q. Conj (prime2 q) (Conj (lt n q) (r3 q))                          ---- *)
fun finBodyAbs nt =
  let val qF = Free("q_fin", natT)
  in Term.lambda qF (mkConj (prime2 qF) (mkConj (ltF nt qF) (r3 qF))) end;

(* the key-lemma RESULT body : %q. Conj (Conj (prime2 q)(dvd q m)) (r3 q) *)
(* keyBodyAbs is already in scope from the foundation delta. *)

val () = out "P3FIN_INSTANTIATORS_READY\n";

(* ============================================================================
   coreFin nF : for a fixed Free n, build
     jT (Ex (%q. Conj (prime2 q) (Conj (lt n q) (r3 q))))
   ============================================================================ *)
fun coreFin nF =
  let
    val factN = fact nF;
    (* ---- fact_pos : n! >= 1, i.e. fact n = Suc P for some witness P (= n!-1) ---- *)
    val le1fn = fact_pos_atF nF;                       (* le (Suc 0)(fact n) = Ex w. fact n = (Suc 0)+w *)
    val PleAbs = Abs("w", natT, oeq factN (add (suc ZeroC) (Bound 0)));   (* body of le 1 (fact n) *)
    val goalEx = mkEx (finBodyAbs nF);

    fun afterPred w (hw : thm) =                        (* hw : oeq (fact n) (add (Suc 0) w) ; P = w *)
      let
        (* fact n = Suc w :  add (Suc 0) w = Suc(0+w) = Suc w *)
        val aS  = addSucF_at (ZeroC, w);                (* (Suc 0 + w) = Suc(0 + w) *)
        val a0  = add0F_at w;                           (* (0 + w) = w *)
        val aS_Sw = oeq_trans OF [aS, Suc_cong OF [a0]];(* (Suc 0 + w) = Suc w *)
        val factN_Sw = oeq_trans OF [hw, aS_Sw];        (* fact n = Suc w *)

        val fourW = mult fourC w;                       (* 4*P *)
        val NN    = add fourW threeC;                   (* N = (4P)+3 *)

        (* ---- r3 N : immediate ; N is literally add (mult 4 w) 3 ---- *)
        val r3N = r3_intro (NN, w) (oeqreflF_at NN);    (* r3 N *)

        (* ---- 1 < N : N = (4P)+3 = Suc(Suc(Suc(4P))) ; le 2 N witness (Suc(4P)) ----
             N = (4P)+3 = Suc(Suc(Suc(4P)))                       [add3_peel]
             add 2 (Suc(4P)) = Suc(Suc(Suc(4P)))                  [addSuc x2]
             so oeq N (add 2 (Suc(4P)))                                            *)
        val n3peel = add3_peel fourW;                   (* (4P)+3 = Suc(Suc(Suc(4P))) *)
        (* add (Suc(Suc 0)) (Suc(4P)) = Suc(add (Suc 0)(Suc(4P))) = Suc(Suc(add 0 (Suc(4P)))) = Suc(Suc(Suc(4P))) *)
        val b1 = addSucF_at (suc ZeroC, suc fourW);     (* (Suc(Suc 0) + Suc(4P)) = Suc((Suc 0)+Suc(4P)) *)
        val b2 = addSucF_at (ZeroC, suc fourW);         (* ((Suc 0)+Suc(4P)) = Suc(0+Suc(4P)) *)
        val b0 = add0F_at (suc fourW);                  (* (0+Suc(4P)) = Suc(4P) *)
        val b2' = oeq_trans OF [b2, Suc_cong OF [b0]];  (* (Suc 0 + Suc(4P)) = Suc(Suc(4P)) *)
        val add2_eval = oeq_trans OF [b1, Suc_cong OF [b2']];   (* (2 + Suc(4P)) = Suc(Suc(Suc(4P))) *)
        (* N = (2 + Suc(4P)) : N = Suc(Suc(Suc(4P))) = (2+Suc(4P)) *)
        val N_add2 = oeq_trans OF [n3peel, oeq_sym OF [add2_eval]];  (* N = add 2 (Suc(4P)) *)
        val lt1N = le_introF (suc (suc ZeroC), NN, suc fourW) N_add2;   (* le 2 N = lt 1 N *)

        (* ---- Suc N = 4*(n!) : Suc((4P)+3) = (4P)+4 = 4+(4P) = 4*(Suc P) = 4*(n!) ---- *)
        (* Suc((4P)+3) = (4P)+(Suc 3) = (4P)+4   [suc_add_at]  ; Suc 3 = 4 definitionally *)
        val sa = suc_add_at (fourW, threeC);            (* Suc((4P)+3) = (4P)+(Suc 3) = (4P)+4 *)
        (* (4P)+4 = 4+(4P)  [add_comm] *)
        val comm4 = addcommF_at (fourW, fourC);         (* ((4P)+4) = (4+(4P)) *)
        (* 4+(4P) = 4*(Suc P)  [mult_Suc_right : 4*(Suc P) = add 4 (4*P)] *)
        val msr = multSrF_at (fourC, w);                (* mult 4 (Suc P) = add 4 (mult 4 P) *)
        val msrs = oeq_sym OF [msr];                    (* (4 + (4P)) = 4*(Suc P) *)
        (* 4*(Suc P) = 4*(n!)  [mult_cong_r factN_Sw backward : fact n = Suc w] *)
        val SwFn = oeq_sym OF [factN_Sw];               (* Suc w = fact n *)
        val congF = mult_cong_rF (fourC, suc w, factN) SwFn;   (* 4*(Suc P) = 4*(n!) *)
        (* SucN_term = suc NN ; chain : Suc N = ... = mult 4 (fact n) *)
        val SucN_chain =
          oeq_trans OF [ Suc_cong OF [oeqreflF_at NN],         (* Suc N = Suc((4P)+3) (refl-wrap, harmless) *)
            oeq_trans OF [ sa,
              oeq_trans OF [ comm4,
                oeq_trans OF [ msrs, congF ] ] ] ];
        (* SucN_chain : Suc N = mult 4 (fact n).  (the leading Suc_cong-refl keeps shape Suc NN) *)

        (* ---- apply the KEY LEMMA at N ---- *)
        val keyEx_N = prime_factor_3mod4_atF NN r3N lt1N;   (* Ex q. (prime2 q /\ q|N) /\ r3 q *)

        fun afterQ q (hq : thm) =                       (* hq : Conj (Conj (prime2 q)(dvd q N)) (r3 q) *)
          let
            val innerC  = mkConj (prime2 q) (dvd q NN);
            val hInner  = conjunct1_atF (innerC, r3 q) hq;        (* Conj (prime2 q)(dvd q N) *)
            val hr3q    = conjunct2_atF (innerC, r3 q) hq;        (* r3 q *)
            val hPrime  = conjunct1_atF (prime2 q, dvd q NN) hInner;   (* prime2 q *)
            val hDvdqN  = conjunct2_atF (prime2 q, dvd q NN) hInner;   (* dvd q N *)
            (* lt 1 q = conjunct1 of prime2 q *)
            val lt1q    = conjunct1_atF (lt (suc ZeroC) q, mkForall (ppAbs q)) hPrime;  (* lt 1 q = le 2 q *)
            (* le 1 q from le 2 q by le_trans (1,2,q) with le_one_two *)
            val le1q    = le_transF_at (suc ZeroC, suc (suc ZeroC), q) le_one_two lt1q;  (* le 1 q *)

            (* ---- CLAIM lt n q ---- *)
            val ltnq =
              let
                val dz = le_totalF_at (suc nF, q);      (* Disj (le (Suc n) q)(le q (Suc n)) *)
                                                        (* le (Suc n) q == lt n q *)
                val caseLt =
                  let val h = Thm.assume (ctermF (jT (ltF nF q)))   (* = le (Suc n) q *)
                  in Thm.implies_intr (ctermF (jT (le (suc nF) q))) h end;
                val casePSn =
                  let
                    val hle = Thm.assume (ctermF (jT (le q (suc nF))));
                    val dc  = le_cases_atF (q, nF) hle;   (* Disj (le q n)(oeq q (Suc n)) *)
                    val subLeqn =
                      let
                        val hleqn = Thm.assume (ctermF (jT (le q nF)));   (* le q n *)
                        val dvdqfn = dvd_fact_atF (q, nF) le1q hleqn;     (* dvd q (fact n) *)
                        (* dvd q (n! * 4) -> dvd q (4 * n!) -> dvd q (Suc N) *)
                        val dvdqfn4 = dvd_mult_right_atF (q, factN, fourC) dvdqfn;  (* dvd q (mult (fact n) 4) *)
                        (* subst (mult (fact n) 4) -> (mult 4 (fact n)) via mult_comm *)
                        val mc = multcommF_at (factN, fourC);             (* (n! * 4) = (4 * n!) *)
                        val z1 = Free("z_dm", natT);
                        val Psub1 = Term.lambda z1 (dvd q z1);
                        val sub1 = beta_norm (Drule.infer_instantiate ctxtF
                              [(("P",0), ctermF Psub1), (("a",0), ctermF (mult factN fourC)),
                               (("b",0), ctermF (mult fourC factN))] oeq_subst_vF);
                        val dvdq4fn = (sub1 OF [mc]) OF [dvdqfn4];        (* dvd q (mult 4 (fact n)) *)
                        (* subst (mult 4 (fact n)) -> (Suc N) via (Suc N = mult 4 (fact n)) sym *)
                        val mc2 = oeq_sym OF [SucN_chain];                (* (mult 4 (fact n)) = Suc N *)
                        val z2 = Free("z_sn", natT);
                        val Psub2 = Term.lambda z2 (dvd q z2);
                        val sub2 = beta_norm (Drule.infer_instantiate ctxtF
                              [(("P",0), ctermF Psub2), (("a",0), ctermF (mult fourC factN)),
                               (("b",0), ctermF (suc NN))] oeq_subst_vF);
                        val dvdqSN = (sub2 OF [mc2]) OF [dvdq4fn];        (* dvd q (Suc N) *)
                        (* consec_coprime : 1<q, q|N, q|Suc N -> oFalse *)
                        val fls = consec_coprime_atF (q, NN) lt1q hDvdqN dvdqSN;   (* oFalse *)
                        val g = (oFalse_elimF_at (ltF nF q)) OF [fls];   (* lt n q *)
                      in Thm.implies_intr (ctermF (jT (le q nF))) g end;
                    val subEq =
                      let
                        val heq = Thm.assume (ctermF (jT (oeq q (suc nF))));   (* oeq q (Suc n) *)
                        val leSnSn = le_reflF_at (suc nF);                    (* le (Suc n)(Suc n) *)
                        val zF   = Free("z_eu", natT);
                        val Psub = Term.lambda zF (le (suc nF) zF);          (* %z. le (Suc n) z *)
                        val subInst = beta_norm (Drule.infer_instantiate ctxtF
                              [(("P",0), ctermF Psub), (("a",0), ctermF (suc nF)), (("b",0), ctermF q)] oeq_subst_vF);
                        val Sn_q = oeq_sym OF [heq];                          (* oeq (Suc n) q *)
                        val g = (subInst OF [Sn_q]) OF [leSnSn];              (* le (Suc n) q = lt n q *)
                      in Thm.implies_intr (ctermF (jT (oeq q (suc nF)))) g end;
                    val combined = disjE_elimF (le q nF, oeq q (suc nF), ltF nF q) dc subLeqn subEq;
                  in Thm.implies_intr (ctermF (jT (le q (suc nF)))) combined end;
                val res = disjE_elimF (le (suc nF) q, le q (suc nF), ltF nF q) dz caseLt casePSn;
              in res end;   (* ltnq : jT (lt n q) *)

            (* ---- build the result conjunction : prime2 q /\ (lt n q /\ r3 q) ---- *)
            val innerConj = conjI_atF (ltF nF q, r3 q) ltnq hr3q;        (* Conj (lt n q)(r3 q) *)
            val fullConj  = conjI_atF (prime2 q, mkConj (ltF nF q) (r3 q)) hPrime innerConj;
                                                                          (* Conj (prime2 q)(Conj (lt n q)(r3 q)) *)
            val ex = exI_atF (finBodyAbs nF) q fullConj;                  (* Ex (%q. ...) *)
          in ex end;

        val resEx = exE_elimF (keyBodyAbs NN, goalEx) keyEx_N "q_fin" afterQ;
      in resEx end;

    val core = exE_elimF (PleAbs, goalEx) le1fn "w_pred" afterPred;
  in core end;

(* ============================================================================
   allI over n  ->  the full theorem
   ============================================================================ *)
val () = out "P3FIN_CORE_READY\n";

val p3mod4_all =
  let
    val nGen = Free("n", natT);
    val coreThm = coreFin nGen;                          (* jT (Ex (%q. Conj (prime2 q)(Conj (lt n q)(r3 q)))) *)
    val PallAbs =
      let val nF = Free("n_all", natT)
      in Term.lambda nF (mkEx (finBodyAbs nF)) end;       (* %n. Ex (%q. ...) *)
    val allThm  = Thm.forall_intr (ctermF nGen) coreThm; (* !!n. jT (Ex (%q. ...)) *)
    val gAll    = allI_atF PallAbs allThm;               (* jT (Forall (%n. ...)) *)
  in varify gAll end;

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal.
   ============================================================================ *)
val p3mod4_intended =
  let
    val nF = Free("n_all", natT)
    val qF = Free("q_fin", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda qF (mkConj (prime2 qF) (mkConj (ltF nF qF) (r3 qF)))))
  in jT (mkForall Pall) end;

val r_p3 = checkP ("p3mod4_all", p3mod4_all, p3mod4_intended);
val () = if r_p3 then out "P3MOD4_OK\n" else out "P3MOD4_FAILED\n";

(* ---- HYP CHECK : Thm.hyps_of = [] ---- *)
val p3_no_hyps = (length (Thm.hyps_of p3mod4_all) = 0);
val () = if p3_no_hyps then out "P3MOD4_NOHYPS_OK\n" else out "P3MOD4_NOHYPS_FAILED\n";

(* ============================================================================
   SOUNDNESS PROBES : the kernel rejects FALSE / DIFFERENT variants.
   ============================================================================ *)
(* probe 1 : flip lt n q -> lt q n (FALSE : take n=0, no prime q<0).  Must NOT aconv. *)
val probe_flip =
  let
    val nF = Free("n_all", natT)
    val qF = Free("q_fin", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda qF (mkConj (prime2 qF) (mkConj (ltF qF nF) (r3 qF)))))
  in not ((Thm.prop_of p3mod4_all) aconv (jT (mkForall Pall))) end;
(* probe 2 : drop the r3 q conjunct (DIFFERENT, weaker statement).  Must NOT aconv. *)
val probe_dropr3 =
  let
    val nF = Free("n_all", natT)
    val qF = Free("q_fin", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda qF (mkConj (prime2 qF) (ltF nF qF))))
  in not ((Thm.prop_of p3mod4_all) aconv (jT (mkForall Pall))) end;
(* probe 3 : drop the prime2 q conjunct (DIFFERENT).  Must NOT aconv. *)
val probe_dropprime =
  let
    val nF = Free("n_all", natT)
    val qF = Free("q_fin", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda qF (mkConj (ltF nF qF) (r3 qF))))
  in not ((Thm.prop_of p3mod4_all) aconv (jT (mkForall Pall))) end;

val () = if probe_flip andalso probe_dropr3 andalso probe_dropprime
         then out "P3MOD4_PROBES_OK\n" else out "P3MOD4_PROBES_UNSOUND\n";

val () = if r_p3 andalso p3_no_hyps andalso probe_flip andalso probe_dropr3 andalso probe_dropprime
         then out "P3MOD4_ALL_OK\n" else out "P3MOD4_ALL_FAILED\n";
