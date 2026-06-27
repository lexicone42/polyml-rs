(* ============================================================================
   W1 POW+POLY -> CRUDE_TAIL DELTA.  Appended AFTER w1_crude_appendix.sml
   (which is appended after bertrand_f7_full.sml).  Final context: ctxtBL.
   THE CRUDE ROUTE, S0 = 36 (clean, mod-free).  Decouples the exponent from
   bitlen : fixed-form b = rdiv (add s 9) 4.
     (POW)  pow_bound  via nat_induct Pc(c): (4c+39)^2 <= 2^(c+11), base
            39^2<=2^11=64*32 by the factored 273<=800 certificate.
     (POLY) poly_ineq  via the scale-by-12 additive argument (div_mod_eq +
            rmod_lt only), polynomial core s^2-33s-74>0 for s>=36.
     (CT)   crude_tail via seb_reduce + seb_tail_reduce + pow_bound + poly_ineq.
   ============================================================================ *)
val () = out "W1_POW_POLY_DELTA_BEGIN\n";

(* ============================================================================
   PROBE 2 : the POW lemma.
     pow_bound : le 36 s ==> le (mult (Suc s)(Suc s))(pow 2 (rdiv (add s 9) 4))
   via the clean nat_induct lemma Pc(c): le (mult A A)(pow 2 (add c 11)), A=4c+39.
   Appended after _w1base.sml (ctxtBL live).
   ============================================================================ *)
val () = out "PROBE2_BEGIN\n";

fun timeit name f =
  let val t0 = Time.now () val r = f () val t1 = Time.now ()
  in out (name ^ " : " ^ Time.toString (Time.- (t1, t0)) ^ "s\n"); r end;

(* ---- distrib + small numeral helpers on ctxtBL ---- *)
val left_distrib_vBL  = varify left_distrib;
val right_distrib_vBL = varify right_distrib;
val () = out ("left_distrib_vBL vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) (Term.add_vars (Thm.prop_of left_distrib_vBL) [])) ^ "\n");
val () = out ("right_distrib_vBL vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) (Term.add_vars (Thm.prop_of right_distrib_vBL) [])) ^ "\n");
(* left_distrib statement : oeq (mult K (add m n))(add (mult K m)(mult K n)) ; the
   "outer" multiplicand var is the induction var (k).  Instantiate by matching. *)
fun ldistBL (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL
        [(("k",0), ctermBL xt),(("m",0), ctermBL mt),(("n",0), ctermBL nt)] left_distrib_vBL);
fun rdistBL (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtBL
        [(("m",0), ctermBL mt),(("n",0), ctermBL nt),(("k",0), ctermBL kt)] right_distrib_vBL);
val mult_1_left_vBL = varify mult_1_left;
fun mult1lBL t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] mult_1_left_vBL);
val add_assoc_vBL = varify add_assoc;
fun addassocBL (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtBL
        [(("m",0), ctermBL mt),(("n",0), ctermBL nt),(("k",0), ctermBL kt)] add_assoc_vBL);

(* le_add_mono_l : le X Y ==> le (add Z X)(add Z Y)  (fixed left addend Z) *)
fun le_add_mono_lBL (Zt, Xt, Yt) hXY =
  let
    (* le (add X Z)(add Y Z) via le_add_mono *)
    val base = le_add_monoBL (Xt, Yt, Zt) hXY            (* le (add X Z)(add Y Z) *)
    val cZX  = addcommBL_at (Zt, Xt)                      (* oeq (add Z X)(add X Z) *)
    val cZY  = addcommBL_at (Zt, Yt)                      (* oeq (add Z Y)(add Y Z) *)
    val l1 = le_cong_lBL (add Xt Zt, add Zt Xt, add Yt Zt) (oeqsymBL cZX) base   (* le (add Z X)(add Y Z) *)
    val l2 = le_cong_rBL (add Zt Xt, add Yt Zt, add Zt Yt) (oeqsymBL cZY) l1     (* le (add Z X)(add Z Y) *)
  in l2 end;

(* numerals *)
val c4  = mkNum 4;
val c8  = mkNum 8;
val c9  = mkNum 9;
val c16 = mkNum 16;
val c39 = mkNum 39;
val c11 = mkNum 11;

(* le 16 A and le 9 A from le 39 A (A = add (mult 4 c) 39) via le_add + small evals *)
(* le 39 A : 39 <= add (mult 4 c) 39 = add 39 (mult 4 c) [comm] ; le_add gives le 39 (add 39 (mult 4 c)) *)
fun le39_A cF =
  let val A = add (mult c4 cF) c39
      val cm = addcommBL_at (mult c4 cF, c39)            (* oeq (add (mult 4 c) 39)(add 39 (mult 4 c)) *)
      val la = le_addBL_at (c39, mult c4 cF)              (* le 39 (add 39 (mult 4 c)) *)
  in le_cong_rBL (c39, add c39 (mult c4 cF), A) (oeqsymBL cm) la end;   (* le 39 A *)

(* ============================================================================
   POLY-STEP LEMMA : le (mult (add A c4)(add A c4))(mult 2 (mult A A))
     given le 16 A, le 9 A.    [ (A+4)^2 <= 2 A^2 ]
   ============================================================================ *)
fun poly_step_lemma A h16A h9A =
  let
    val AA = mult A A
    (* expand (A+4)*(A+4) = add (mult A (add A 4))(mult 4 (add A 4))  [right_distrib m=A,n=4,k=A+4] *)
    val e0 = rdistBL (A, c4, add A c4)                    (* oeq (mult (add A 4)(add A 4))(add (mult A (add A 4))(mult 4 (add A 4))) *)
    (* mult A (add A 4) = add (mult A A)(mult A 4) [left_distrib x=A,m=A,n=4] *)
    val eL = ldistBL (A, A, c4)                           (* oeq (mult A (add A 4))(add (mult A A)(mult A 4)) *)
    (* mult 4 (add A 4) = add (mult 4 A)(mult 4 4) [left_distrib x=4,m=A,n=4] *)
    val eR = ldistBL (c4, A, c4)                          (* oeq (mult 4 (add A 4))(add (mult 4 A)(mult 4 4)) *)
    (* combine: LHS = add (add (mult A A)(mult A 4))(add (mult 4 A)(mult 4 4)) *)
    val step1 = oeqtransBL OF [e0,
       oeqtransBL OF [
         add_cong_lBL (mult A (add A c4), add (mult A A)(mult A c4), mult c4 (add A c4)) eL,
         add_cong_rBL (add (mult A A)(mult A c4), mult c4 (add A c4), add (mult c4 A)(mult c4 c4)) eR ]]
       (* oeq (mult (add A 4)(add A 4))(add (add (mult A A)(mult A 4))(add (mult 4 A)(mult 4 4))) *)
    (* reassoc : add (add (A*A) T1)(add T2 T3) = add (A*A)(add T1 (add T2 T3)) [add_assoc] *)
    val T1 = mult A c4 val T2 = mult c4 A val T3 = mult c4 c4
    val rea = addassocBL (mult A A, T1, add T2 T3)        (* oeq (add (add (A*A) T1)(add T2 T3))(add (A*A)(add T1 (add T2 T3))) *)
    val step2 = oeqtransBL OF [step1, rea]
       (* oeq (mult (add A 4)(add A 4))(add (A*A)(add T1 (add T2 T3))) *)
    val REST = add T1 (add T2 T3)
    (* show le REST (A*A) :
       T1 = mult A 4 = mult 4 A [comm] ; T3 = 16.
       REST = add (mult 4 A)(add (mult 4 A) 16)  [after rewriting T1, T3]
            = add (add (mult 4 A)(mult 4 A)) 16  [assoc rev]
            = add (mult 8 A) 16                   [mult 8 A = add (mult 4 A)(mult 4 A)]
       le (add (mult 8 A) 16)(mult 9 A) from le 16 A (since mult 9 A = add (mult 8 A) A)
       le (mult 9 A)(mult A A) from le 9 A. *)
    val cmT1 = multcommBL_at (A, c4)                       (* oeq (mult A 4)(mult 4 A) *)
    val (t3v, t3eq) = mult_eval c4 c4                      (* (16, oeq (mult 4 4) 16) *)
    (* rewrite REST: T1 -> mult 4 A, T3 -> 16 *)
    val REST1 = add T2 (add T2 c16)                        (* = add (mult 4 A)(add (mult 4 A) 16) *)
    val restEq1 = add_cong_lBL (T1, T2, add T2 T3) cmT1    (* oeq (add T1 (add T2 T3))(add T2 (add T2 T3)) *)
    val restEq2 = add_cong_rBL (T2, add T2 T3, add T2 c16) (add_cong_rBL (T2, T3, c16) t3eq)
                  (* oeq (add T2 (add T2 T3))(add T2 (add T2 16)) *)
    val restEq = oeqtransBL OF [restEq1, restEq2]          (* oeq REST (add T2 (add T2 16)) = oeq REST REST1 *)
    (* REST1 = add (add (mult 4 A)(mult 4 A)) 16  [assoc rev] *)
    val reaR = addassocBL (T2, T2, c16)                   (* oeq (add (add T2 T2) 16)(add T2 (add T2 16)) *)
    (* mult 8 A = add (mult 4 A)(mult 4 A) : mult (add 4 4) A = add (mult 4 A)(mult 4 A) [right_distrib] *)
    val (eight, eightEq) = add_eval c4 c4                 (* (8, oeq (add 4 4) 8) *)
    val m8A_split = rdistBL (c4, c4, A)                    (* oeq (mult (add 4 4) A)(add (mult 4 A)(mult 4 A)) *)
    (* want oeq (mult 8 A)(add T2 T2) :
       mult 8 A = mult (add 4 4) A  [mult_cong_lBL on 8 = add 4 4]
                = add (mult 4 A)(mult 4 A)  [m8A_split] *)
    val m8_eq_add44 = mult_cong_lBL (c8, add c4 c4, A) (oeqsymBL eightEq)   (* oeq (mult 8 A)(mult (add 4 4) A) *)
    val m8A_eq2 = oeqtransBL OF [m8_eq_add44, m8A_split]  (* oeq (mult 8 A)(add T2 T2) *)
    (* REST = REST1 = add (add T2 T2) 16 = add (mult 8 A) 16 *)
    val REST_to_8A16 =
      oeqtransBL OF [restEq,
        oeqtransBL OF [oeqsymBL reaR,
          add_cong_lBL (add T2 T2, mult c8 A, c16) (oeqsymBL m8A_eq2)]]
      (* oeq REST (add (mult 8 A) 16) *)
    (* le (add (mult 8 A) 16)(mult 9 A) :
       mult 9 A = add (mult 8 A)(mult 1 A) = add (mult 8 A) A  [right_distrib (8,1,A); mult 1 A = A] *)
    val (nine, nineEq) = add_eval c8 (mkNum 1)            (* (9, oeq (add 8 1) 9) *)
    val m9split = rdistBL (c8, mkNum 1, A)               (* oeq (mult (add 8 1) A)(add (mult 8 A)(mult 1 A)) *)
    val m1A = mult1lBL A                                  (* oeq (mult 1 A) A *)
    val m9_eq_add81 = mult_cong_lBL (c9, add c8 (mkNum 1), A) (oeqsymBL nineEq)   (* oeq (mult 9 A)(mult (add 8 1) A) *)
    val m9_eq = oeqtransBL OF [m9_eq_add81,
                  oeqtransBL OF [m9split, add_cong_rBL (mult c8 A, mult (mkNum 1) A, A) m1A]]
                (* oeq (mult 9 A)(add (mult 8 A) A) *)
    val le_8A16_9A_pre = le_add_mono_lBL (mult c8 A, c16, A) h16A   (* le (add (mult 8 A) 16)(add (mult 8 A) A) *)
    val le_8A16_9A = le_cong_rBL (add (mult c8 A) c16, add (mult c8 A) A, mult c9 A) (oeqsymBL m9_eq) le_8A16_9A_pre
                     (* le (add (mult 8 A) 16)(mult 9 A) *)
    (* le (mult 9 A)(mult A A) : mult_le_mono2 (9,A,A,A) (le 9 A)(le_refl A) *)
    val le_9A_AA = mult_le_mono2BL (c9, A, A, A) h9A (le_reflBL_at A)   (* le (mult 9 A)(mult A A) *)
    val le_REST_AA0 = le_transBL_at (add (mult c8 A) c16, mult c9 A, mult A A) le_8A16_9A le_9A_AA
                      (* le (add (mult 8 A) 16)(mult A A) *)
    val le_REST_AA = le_cong_lBL (add (mult c8 A) c16, REST, mult A A) (oeqsymBL REST_to_8A16) le_REST_AA0
                     (* le REST (A*A) *)
    (* le (add (A*A) REST)(add (A*A)(A*A)) via le_add_mono_l *)
    val le_lhs_dbl = le_add_mono_lBL (mult A A, REST, mult A A) le_REST_AA
                     (* le (add (A*A) REST)(add (A*A)(A*A)) *)
    (* rewrite add (A*A) REST <- mult (A+4)(A+4) [step2 sym]; add (A*A)(A*A) -> mult 2 (A*A) [double] *)
    val lhs_eq = step2                                    (* oeq (mult (add A 4)(add A 4))(add (A*A) REST) *)
    val dbl = mult2_is_double_BL (mult A A)               (* oeq (mult 2 (A*A))(add (A*A)(A*A)) *)
    val g1 = le_cong_lBL (add (mult A A) REST, mult (add A c4)(add A c4), add (mult A A)(mult A A)) (oeqsymBL lhs_eq) le_lhs_dbl
             (* le (mult (A+4)(A+4))(add (A*A)(A*A)) *)
    val g2 = le_cong_rBL (mult (add A c4)(add A c4), add (mult A A)(mult A A), mult twoC (mult A A)) (oeqsymBL dbl) g1
             (* le (mult (A+4)(A+4))(mult 2 (A*A)) *)
  in g2 end;

val () = out "POLY_STEP_LEMMA_DEFINED\n";
val () = out "P2BODY_DONE\n";

(* ============================================================================
   PROBE 4 : full Pc induction (base un-nested probe3d style + step) + nat_induct.
   Then the connection -> pow_bound.
   ============================================================================ *)
val () = out "PROBE4_BEGIN\n";
val n0  = mkNum 0;  val n4 = mkNum 4; val n7 = mkNum 7; val n8 = mkNum 8; val n9 = mkNum 9;
val n11 = mkNum 11; val n16 = mkNum 16; val n25 = mkNum 25; val n32 = mkNum 32;
val n39 = mkNum 39; val n64 = mkNum 64;
fun evalAdd a b = #2 (add_eval (mkNum a) (mkNum b));
fun evalMul a b = #2 (mult_eval (mkNum a) (mkNum b));
fun Aof c = add (mult n4 c) n39;
val cPc = Free("c_Pc", natT);
val Pc_pred = Term.lambda cPc (le (mult (Aof cPc)(Aof cPc))(pow twoC (add cPc n11)));

(* le39_A, le16_A, le9_A *)
fun le39_A cF =
  let val A = Aof cF
      val cm = addcommBL_at (mult n4 cF, n39)
      val la = le_addBL_at (n39, mult n4 cF)
  in le_cong_rBL (n39, add n39 (mult n4 cF), A) (oeqsymBL cm) la end;
fun le16_A cF = le_transBL_at (n16, n39, Aof cF) (le_evalBL 16 39) (le39_A cF);
fun le9_A  cF = le_transBL_at (n9,  n39, Aof cF) (le_evalBL 9 39) (le39_A cF);

(* ---- Pc(0) base : un-nested probe3d structure ---- *)
fun evalPow2 0 = (suc ZeroC, powZeroBL_at twoC)
  | evalPow2 k =
      let val (rv, rth) = evalPow2 (k-1)
          val ps = powSucBL_at (twoC, mkNum (k-1))
          val cong = mult_cong_rBL (twoC, pow twoC (mkNum (k-1)), rv) rth
          val (mv, mth) = mult_eval twoC rv
      in (mv, oeqtransBL OF [ps, oeqtransBL OF [cong, mth]]) end;
val A0 = Aof n0;
val m40 = mult0r_BL_at n4;
val a039 = oeqtransBL OF [add_cong_lBL (mult n4 n0, n0, n39) m40, add0BL_at n39];
val a011 = add0BL_at n11;
val (p6v, p6th) = evalPow2 6;
val (p5v, p5th) = evalPow2 5;
val pe = pow_addBL_at (twoC, mkNum 6, mkNum 5);
val a65 = evalAdd 6 5;
val p11_eq_6566 = oeqtransBL OF [pow_cong_eBL (twoC, mkNum 11, add (mkNum 6)(mkNum 5)) (oeqsymBL a65), pe];
val p11_eq_6432 = oeqtransBL OF [p11_eq_6566,
      oeqtransBL OF [mult_cong_lBL (pow twoC (mkNum 6), p6v, pow twoC (mkNum 5)) p6th,
                     mult_cong_rBL (p6v, pow twoC (mkNum 5), p5v) p5th]];
val e3927 = evalAdd 32 7;
val l1 = mult_cong_lBL (add n32 n7, n39, n39) e3927;
val l2 = rdistBL (n32, n7, n39);
val lhs_eq = oeqtransBL OF [oeqsymBL l1, l2];
val e3925_64 = evalAdd 39 25;
val r1 = multcommBL_at (n64, n32);
val r2 = mult_cong_rBL (n32, n64, add n39 n25) (oeqsymBL e3925_64);
val r3 = ldistBL (n32, n39, n25);
val rhs_eq = oeqtransBL OF [r1, oeqtransBL OF [r2, r3]];
val e739 = evalMul 7 39;
val e3225 = evalMul 32 25;
val le273_800 = le_evalBL 273 800;
val le_739_3225 = le_cong_rBL (mult n7 n39, mkNum 800, mult n32 n25)
      (oeqsymBL e3225) (le_cong_lBL (mkNum 273, mult n7 n39, mkNum 800) (oeqsymBL e739) le273_800);
val le_sums = le_add_mono_lBL (mult n32 n39, mult n7 n39, mult n32 n25) le_739_3225;
val bg1 = le_cong_lBL (add (mult n32 n39)(mult n7 n39), mult n39 n39, add (mult n32 n39)(mult n32 n25)) (oeqsymBL lhs_eq) le_sums;
val bg2 = le_cong_rBL (mult n39 n39, add (mult n32 n39)(mult n32 n25), mult n64 n32) (oeqsymBL rhs_eq) bg1;
val base3939 = le_cong_rBL (mult n39 n39, mult n64 n32, pow twoC n11) (oeqsymBL p11_eq_6432) bg2;
val mcl = mult_cong_lBL (A0, n39, A0) a039;
val mcr = mult_cong_rBL (n39, A0, n39) a039;
val both = oeqtransBL OF [mcl, mcr];
val lhsB = le_cong_lBL (mult n39 n39, mult A0 A0, pow twoC n11) (oeqsymBL both) base3939;
val Pc_base = le_cong_rBL (mult A0 A0, pow twoC n11, pow twoC (add n0 n11))
          (pow_cong_eBL (twoC, n11, add n0 n11) (oeqsymBL a011)) lhsB;
val () = out ("Pc_base : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of Pc_base) ^ "\n");
val () = out "PC_BASE_OK\n";

(* ---- Pc step : !!c. Pc c ==> Pc (Suc c) ---- *)
fun Pc_step cF IH =   (* IH : le (mult (Aof c)(Aof c))(pow 2 (add c 11)) *)
  let
    val A = Aof cF
    val A' = Aof (suc cF)   (* add (mult 4 (Suc c)) 39 *)
    (* A' = add A 4 : mult 4 (Suc c) = add 4 (mult 4 c) [mult_Suc_right via mult_Sr_BL_at (c, 4)] *)
    val mS = mult_Sr_BL_at (n4, cF)        (* oeq (mult 4 (Suc c))(add 4 (mult 4 c)) *)
    (* A' = add (mult 4 (Suc c)) 39 -> add (add 4 (mult 4 c)) 39 *)
    val A'1 = add_cong_lBL (mult n4 (suc cF), add n4 (mult n4 cF), n39) mS   (* oeq A' (add (add 4 (mult 4 c)) 39) *)
    (* rearrange (4 + 4c) + 39 = (4c + 39) + 4 = add A 4 *)
    val s1 = add_cong_lBL (add n4 (mult n4 cF), add (mult n4 cF) n4, n39) (addcommBL_at (n4, mult n4 cF))
             (* oeq (add (add 4 (mult 4 c)) 39)(add (add (mult 4 c) 4) 39) *)
    val s2 = addassocBL (mult n4 cF, n4, n39)   (* oeq (add (add (mult 4 c) 4) 39)(add (mult 4 c)(add 4 39)) *)
    val s3 = add_cong_rBL (mult n4 cF, add n4 n39, add n39 n4) (addcommBL_at (n4, n39))
             (* oeq (add (mult 4 c)(add 4 39))(add (mult 4 c)(add 39 4)) *)
    val s4 = oeqsymBL (addassocBL (mult n4 cF, n39, n4))   (* oeq (add (mult 4 c)(add 39 4))(add (add (mult 4 c) 39) 4) = add A 4 *)
    val A'eqA4 = oeqtransBL OF [A'1, oeqtransBL OF [s1, oeqtransBL OF [s2, oeqtransBL OF [s3, s4]]]]
                 (* oeq A' (add A 4) *)
    (* poly_step_lemma A : le (mult (add A 4)(add A 4))(mult 2 (mult A A)) *)
    val psl = poly_step_lemma A (le16_A cF) (le9_A cF)
              (* le (mult (add A 4)(add A 4))(mult 2 (mult A A)) *)
    (* mult 2 (mult A A) <= mult 2 (pow 2 (add c 11)) [mult_le_mono on IH] *)
    val mono = mult_le_monoBL (twoC, mult A A, pow twoC (add cF n11)) IH
               (* le (mult 2 (mult A A))(mult 2 (pow 2 (add c 11))) *)
    (* mult 2 (pow 2 (add c 11)) = pow 2 (Suc(add c 11)) [pow_Suc sym] *)
    val pS = powSucBL_at (twoC, add cF n11)   (* oeq (pow 2 (Suc(add c 11)))(mult 2 (pow 2 (add c 11))) *)
    (* Suc(add c 11) = add (Suc c) 11 [add_Suc sym] *)
    val aS = addSucBL_at (cF, n11)            (* oeq (add (Suc c) 11)(Suc(add c 11)) *)
    (* chain : le (mult (add A 4)(add A 4))(mult 2 (mult A A)) <= (mult 2 (pow 2 (add c 11))) *)
    val ch1 = le_transBL_at (mult (add A n4)(add A n4), mult twoC (mult A A), mult twoC (pow twoC (add cF n11))) psl mono
              (* le (mult (add A 4)(add A 4))(mult 2 (pow 2 (add c 11))) *)
    (* rewrite RHS mult 2 (pow 2 (add c 11)) -> pow 2 (Suc(add c 11)) -> pow 2 (add (Suc c) 11) *)
    val ch2 = le_cong_rBL (mult (add A n4)(add A n4), mult twoC (pow twoC (add cF n11)), pow twoC (suc (add cF n11)))
              (oeqsymBL pS) ch1
              (* le (mult (add A 4)(add A 4))(pow 2 (Suc(add c 11))) *)
    val ch3 = le_cong_rBL (mult (add A n4)(add A n4), pow twoC (suc (add cF n11)), pow twoC (add (suc cF) n11))
              (pow_cong_eBL (twoC, suc (add cF n11), add (suc cF) n11) (oeqsymBL aS)) ch2
              (* le (mult (add A 4)(add A 4))(pow 2 (add (Suc c) 11)) *)
    (* rewrite LHS mult (add A 4)(add A 4) -> mult A' A' via A'eqA4 (reversed) on both factors *)
    val lcong = oeqtransBL OF [mult_cong_lBL (add A n4, A', add A n4) (oeqsymBL A'eqA4),
                               mult_cong_rBL (A', add A n4, A') (oeqsymBL A'eqA4)]
                (* oeq (mult (add A 4)(add A 4))(mult A' A') *)
    val g = le_cong_lBL (mult (add A n4)(add A n4), mult A' A', pow twoC (add (suc cF) n11)) lcong ch3
            (* le (mult A' A')(pow 2 (add (Suc c) 11)) = Pc(Suc c) *)
  in g end;

val () =
  (let val cF = Free("c_stp", natT)
       val IH = Thm.assume (ctermBL (jT (le (mult (Aof cF)(Aof cF))(pow twoC (add cF n11)))))
       val th = Pc_step cF IH
   in out ("Pc_step : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n") end)
  handle e => out ("Pc_step EXN : " ^ General.exnMessage e ^ "\n");
val () = out "PC_STEP_DONE\n";

val () = out "P4BODY_DONE\n";

(* ============================================================================
   PROBE 5 : Pc assembly (nat_induct) + connection -> pow_bound.
   Requires Pc_base (val) + Pc_step (fun) + le39_A/le16_A/le9_A + Aof, all live.
   ============================================================================ *)
val () = out "PROBE5_BEGIN\n";

(* ---- assemble Pc : !c. le (mult (Aof c)(Aof c))(pow 2 (add c 11)) ---- *)
val Pc_thm =
  let
    val kTop = Free("c_top_pc", natT)
    val indThm = nat_induct_BL (Pc_pred, kTop)
    val cF = Free("c_step_pc", natT)
    val IHp = jT (le (mult (Aof cF)(Aof cF))(pow twoC (add cF n11)))
    val IH = Thm.assume (ctermBL IHp)
    val stepConcl = Pc_step cF IH
    val stepMeta = Thm.forall_intr (ctermBL cF) (Thm.implies_intr (ctermBL IHp) stepConcl)
    val concl = Thm.implies_elim (Thm.implies_elim indThm Pc_base) stepMeta
  in varify concl end;
val () = out ("Pc_thm 0hyp=" ^ Bool.toString (zhBL Pc_thm) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of Pc_thm) ^ "\n");
val Pc_var = hd (Term.add_vars (Thm.prop_of Pc_thm) []);
fun Pc_at c = beta_norm (Drule.infer_instantiate ctxtBL [(fst Pc_var, ctermBL c)] Pc_thm);
val () = out "PC_THM_OK\n";

(* ---- connection helpers ---- *)
val n3 = mkNum 3; val n10 = mkNum 10; val n36 = mkNum 36;
val n40 = mkNum 40; val n43 = mkNum 43; val n44 = mkNum 44; val n45 = mkNum 45;
val lt0_4 = lt_evalBL 0 4;   (* lt 0 4 = le 1 4 *)
(* add_right_cancel via add_left_cancel + comm *)
val add_left_cancel_vBL = varify add_left_cancel;
fun add_left_cancelBL (mt, at, bt) h =
  beta_norm (Drule.infer_instantiate ctxtBL
    [(("m",0), ctermBL mt),(("a",0), ctermBL at),(("b",0), ctermBL bt)] add_left_cancel_vBL) OF [h];
fun add_right_cancelBL (at, bt, kt) h =
  let val cmA = addcommBL_at (at, kt) val cmB = addcommBL_at (bt, kt)
      val h2 = oeqtransBL OF [oeqsymBL cmA, oeqtransBL OF [h, cmB]]
  in add_left_cancelBL (kt, at, bt) h2 end;

(* ============================================================================
   pow_bound : le 36 s ==> le (mult (Suc s)(Suc s))(pow 2 (rdiv (add s 9) 4))
   ============================================================================ *)
fun pow_bound_body sF hLe36 =   (* hLe36 : le 36 s *)
  let
    val s9 = add sF n9
    val b  = rdiv s9 n4
    val r  = rmod s9 n4
    (* div_mod : oeq (add s 9)(add (mult 4 b) r) *)
    val dme = div_mod_eqBL (s9, n4) lt0_4
    (* rmod_lt : lt r 4 -> le r 3 *)
    val rlt = rmod_ltBL (s9, n4) lt0_4         (* lt r 4 = le (Suc r) 4 *)
    val r_le3 = le_suc_inv_BL (r, n3) rlt       (* le r 3   (4 = Suc 3) *)
    (* le 45 (add s 9) : le 36 s -> le (add 36 9)(add s 9) -> le 45 (add s 9) *)
    val le36_9 = le_add_monoBL (n36, sF, n9) hLe36      (* le (add 36 9)(add s 9) *)
    val e369 = #2 (add_eval n36 n9)                      (* oeq (add 36 9) 45 *)
    val le45_s9 = le_cong_lBL (add n36 n9, mkNum 45, s9) e369 le36_9   (* le 45 (add s 9) *)
    (* ---- le 11 b : by contradiction (assume lt b 11 = le (Suc b) 11) ---- *)
    val le11_b =
      let
        val hAss = Thm.assume (ctermBL (jT (le (suc b) n11)))    (* lt b 11 *)
        val le_b10 = le_suc_inv_BL (b, n10) hAss                  (* le b 10  (11 = Suc 10) *)
        val le_4b40 = mult_le_monoBL (n4, b, n10) le_b10          (* le (mult 4 b)(mult 4 10) *)
        val e4_10 = #2 (mult_eval n4 n10)                         (* oeq (mult 4 10) 40 *)
        val le_4b_40 = le_cong_rBL (mult n4 b, mult n4 n10, n40) e4_10 le_4b40   (* le (mult 4 b) 40 *)
        (* le (add (mult 4 b) r)(add 40 r) [le_add_mono fix r] *)
        val le_sum1 = le_add_monoBL (mult n4 b, n40, r) le_4b_40   (* le (add (mult 4 b) r)(add 40 r) *)
        (* le (add 40 r)(add 40 3) [le_add_mono_l fix 40] *)
        val le_sum2 = le_add_mono_lBL (n40, r, n3) r_le3           (* le (add 40 r)(add 40 3) *)
        val e40_3 = #2 (add_eval n40 n3)                          (* oeq (add 40 3) 43 *)
        val le_sum2b = le_cong_rBL (add n40 r, add n40 n3, n43) e40_3 le_sum2   (* le (add 40 r) 43 *)
        val le_s9form_43 = le_transBL_at (add (mult n4 b) r, add n40 r, n43) le_sum1 le_sum2b   (* le (add (mult 4 b) r) 43 *)
        (* le (add s 9) 43 [rewrite (add (mult 4 b) r) <- (add s 9) via dme] *)
        val le_s9_43 = le_cong_lBL (add (mult n4 b) r, s9, n43) (oeqsymBL dme) le_s9form_43   (* le (add s 9) 43 *)
        (* le 45 43 [trans le45_s9 + le_s9_43] -> oFalse *)
        val le45_43 = le_transBL_at (mkNum 45, s9, n43) le45_s9 le_s9_43   (* le 45 43 *)
        (* 45 = Suc 44 ; le 43 44 (le_suc_self) ; le (Suc 44) 43 + le 43 44 -> le (Suc 44) 44 = lt 44 44 -> false *)
        val le43_44 = le_suc_selfBL_at n43                       (* le 43 (Suc 43) = le 43 44 *)
        val le_S44_44 = le_transBL_at (suc n44, n43, suc n43) le45_43 le43_44   (* le (Suc 44) 44 ... need 45=Suc 44, 44=Suc 43 *)
        (* note: 45 = mkNum 45 = suc(mkNum 44) = suc n44 definitionally; 44 = mkNum 44 = suc(mkNum 43)=suc n43 *)
        val ff = lt_irreflBL_at n44 OF [le_S44_44]               (* oFalse  (lt 44 44 = le (Suc 44) 44) *)
        val negImp = impI_BL (lt b n11, oFalseC) (Thm.implies_intr (ctermBL (jT (le (suc b) n11))) ff)  (* neg (lt b 11) *)
      in nlt_leBL (b, n11) negImp end   (* le 11 b *)
    (* ---- exE le 11 b : witness e, oeq b (add 11 e) ---- *)
    val goalC = le (mult (suc sF)(suc sF))(pow twoC b)
    val Pe = Abs("e_pb", natT, oeq b (add n11 (Bound 0)))
    fun ebody eF (he : thm) =   (* he : oeq b (add 11 e) *)
      let
        val Ae = Aof eF
        (* pow 2 (add e 11) = pow 2 b : oeq b (add 11 e) -> oeq b (add e 11) [comm] -> rewrite *)
        val b_eq_e11 = oeqtransBL OF [he, addcommBL_at (n11, eF)]   (* oeq b (add e 11) *)
        val Pc_e = Pc_at eF                          (* le (mult (Aof e)(Aof e))(pow 2 (add e 11)) *)
        val Pc_e_b = le_cong_rBL (mult Ae Ae, pow twoC (add eF n11), pow twoC b)
              (pow_cong_eBL (twoC, add eF n11, b) (oeqsymBL b_eq_e11)) Pc_e
              (* le (mult (Aof e)(Aof e))(pow 2 b) *)
        (* ---- le (Suc s)(Aof e) ---- *)
        (* mult 4 b = mult 4 (add 11 e) = add (mult 4 11)(mult 4 e) = add 44 (mult 4 e) *)
        val m4b_1 = mult_cong_rBL (n4, b, add n11 eF) he           (* oeq (mult 4 b)(mult 4 (add 11 e)) *)
        val m4b_2 = ldistBL (n4, n11, eF)                          (* oeq (mult 4 (add 11 e))(add (mult 4 11)(mult 4 e)) *)
        val e4_11 = #2 (mult_eval n4 n11)                          (* oeq (mult 4 11) 44 *)
        val m4b_3 = add_cong_lBL (mult n4 n11, n44, mult n4 eF) e4_11   (* oeq (add (mult 4 11)(mult 4 e))(add 44 (mult 4 e)) *)
        val m4b_eq = oeqtransBL OF [m4b_1, oeqtransBL OF [m4b_2, m4b_3]]   (* oeq (mult 4 b)(add 44 (mult 4 e)) *)
        (* dme : add s 9 = add (mult 4 b) r ; rewrite -> add (add 44 (4e)) r *)
        val s9_eq_form = oeqtransBL OF [dme, add_cong_lBL (mult n4 b, add n44 (mult n4 eF), r) m4b_eq]
                         (* oeq (add s 9)(add (add 44 (4e)) r) *)
        (* add s 9 = add (Suc s) 8 *)
        val s9_S8 = oeqtransBL OF [add_Sr_BL_at (sF, n8), oeqsymBL (addSucBL_at (sF, n8))]
                    (* oeq (add s 9)(add (Suc s) 8) : add s (Suc 8)=Suc(add s 8); add (Suc s) 8 = Suc(add s 8) *)
        (* add (add 44 (4e)) r = add (add (add 36 (4e)) r) 8 :
           44 = add 36 8 ; rearrange (36+8 + 4e) + r = ((36+4e)+r) + 8 *)
        val e44 = #2 (add_eval n36 n8)                            (* oeq (add 36 8) 44 *)
        (* 44 + 4e = (36+8) + 4e = 36 + (8 + 4e) = 36 + (4e + 8) = (36 + 4e) + 8 *)
        val rr1 = add_cong_lBL (n44, add n36 n8, mult n4 eF) (oeqsymBL e44)   (* oeq (add 44 (4e))(add (add 36 8)(4e)) *)
        val rr2 = addassocBL (n36, n8, mult n4 eF)                (* oeq (add (add 36 8)(4e))(add 36 (add 8 (4e))) *)
        val rr3 = add_cong_rBL (n36, add n8 (mult n4 eF), add (mult n4 eF) n8) (addcommBL_at (n8, mult n4 eF))
                  (* oeq (add 36 (add 8 (4e)))(add 36 (add (4e) 8)) *)
        val rr4 = oeqsymBL (addassocBL (n36, mult n4 eF, n8))     (* oeq (add 36 (add (4e) 8))(add (add 36 (4e)) 8) *)
        val sum44_4e = oeqtransBL OF [rr1, oeqtransBL OF [rr2, oeqtransBL OF [rr3, rr4]]]
                       (* oeq (add 44 (4e))(add (add 36 (4e)) 8) *)
        (* (add 44 (4e)) + r = (add (36+4e) 8) + r = (add (36+4e) r) + 8  [reassoc swap 8<->r] *)
        val lhs1 = add_cong_lBL (add n44 (mult n4 eF), add (add n36 (mult n4 eF)) n8, r) sum44_4e
                   (* oeq (add (add 44 (4e)) r)(add (add (add 36 (4e)) 8) r) *)
        (* (X + 8) + r = X + (8 + r) = X + (r + 8) = (X + r) + 8 , X = add 36 (4e) *)
        val X36 = add n36 (mult n4 eF)
        val sw1 = addassocBL (X36, n8, r)                        (* oeq (add (add X 8) r)(add X (add 8 r)) *)
        val sw2 = add_cong_rBL (X36, add n8 r, add r n8) (addcommBL_at (n8, r))   (* oeq (add X (add 8 r))(add X (add r 8)) *)
        val sw3 = oeqsymBL (addassocBL (X36, r, n8))             (* oeq (add X (add r 8))(add (add X r) 8) *)
        val swap8r = oeqtransBL OF [sw1, oeqtransBL OF [sw2, sw3]]   (* oeq (add (add X 8) r)(add (add X r) 8) *)
        val rhs_form = oeqtransBL OF [lhs1, swap8r]             (* oeq (add (add 44 (4e)) r)(add (add X r) 8) *)
        (* assemble : add (Suc s) 8 = add s 9 = add (add 44 (4e)) r = add (add X r) 8 *)
        val chain = oeqtransBL OF [oeqsymBL s9_S8, oeqtransBL OF [s9_eq_form, rhs_form]]
                    (* oeq (add (Suc s) 8)(add (add X r) 8) *)
        val cancel = add_right_cancelBL (suc sF, add X36 r, n8) chain   (* oeq (Suc s)(add X r) , X = add 36 (4e) *)
        (* le (Suc s)(Aof e) : suffices le (add X r)(add (4e) 39) ; X r = (36+4e)+r *)
        (* (36+4e)+r = 4e + (36 + r)  [comm 36<->4e then assoc] *)
        val q1 = add_cong_lBL (X36, add (mult n4 eF) n36, r) (addcommBL_at (n36, mult n4 eF))   (* oeq (add X r)(add (add (4e) 36) r) *)
        val q2 = addassocBL (mult n4 eF, n36, r)                (* oeq (add (add (4e) 36) r)(add (4e)(add 36 r)) *)
        val Xr_eq = oeqtransBL OF [q1, q2]                      (* oeq (add X r)(add (4e)(add 36 r)) *)
        (* le (add 36 r) 39 from le r 3 : le (add 36 r)(add 36 3) -> le (add 36 r) 39 *)
        val le_36r_363 = le_add_mono_lBL (n36, r, n3) r_le3     (* le (add 36 r)(add 36 3) *)
        val e363 = #2 (add_eval n36 n3)                          (* oeq (add 36 3) 39 *)
        val le_36r_39 = le_cong_rBL (add n36 r, add n36 n3, n39) e363 le_36r_363   (* le (add 36 r) 39 *)
        (* le (add (4e)(add 36 r))(add (4e) 39) [le_add_mono_l fix 4e] *)
        val le_q_ae = le_add_mono_lBL (mult n4 eF, add n36 r, n39) le_36r_39   (* le (add (4e)(add 36 r))(add (4e) 39) *)
        (* add (4e) 39 = Aof e *)
        (* le (add X r)(add (4e) 39) via Xr_eq *)
        val le_Xr_ae = le_cong_lBL (add (mult n4 eF)(add n36 r), add X36 r, add (mult n4 eF) n39) (oeqsymBL Xr_eq) le_q_ae
                       (* le (add X r)(add (4e) 39) = le (add X r)(Aof e) *)
        (* le (Suc s)(Aof e) : rewrite (add X r) <- (Suc s) via cancel *)
        val le_Ss_ae = le_cong_lBL (add X36 r, suc sF, Ae) (oeqsymBL cancel) le_Xr_ae   (* le (Suc s)(Aof e) *)
        (* le (mult (Suc s)(Suc s))(mult (Aof e)(Aof e)) *)
        val le_sq = mult_le_mono2BL (suc sF, Ae, suc sF, Ae) le_Ss_ae le_Ss_ae
                    (* le (mult (Suc s)(Suc s))(mult (Aof e)(Aof e)) *)
        (* chain with Pc_e_b *)
        val g = le_transBL_at (mult (suc sF)(suc sF), mult Ae Ae, pow twoC b) le_sq Pc_e_b
                (* le (mult (Suc s)(Suc s))(pow 2 b) *)
      in g end
  in exE_elimBL (Pe, goalC) le11_b "e_pbw" ebody end;

val pow_bound =
  (let
     val sF = Free("s_pb", natT)
     val hLe36 = Thm.assume (ctermBL (jT (le n36 sF)))
     val body = pow_bound_body sF hLe36
     val d1 = Thm.implies_intr (ctermBL (jT (le n36 sF))) body
   in SOME (varify d1) end)
  handle e => (out ("pow_bound EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val () = (case pow_bound of
    SOME th => out ("pow_bound 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
  | NONE => out "pow_bound NONE\n");
val pow_bound_ok = (case pow_bound of SOME th => zhBL th | NONE => false);
val () = if pow_bound_ok then out "POW_BOUND_OK\n" else out "POW_BOUND_FAIL\n";

val () = out "PROBE5_DONE\n";

(* ============================================================================
   PROBE 7 : COMPLETE poly_ineq.
     poly_ineq : le 36 s ==> le (mult s s)(add n n)
        ==> lt (mult (Suc(Suc s))(rdiv (add s 9) 4))(mult 2 (rdiv n 3))
   ============================================================================ *)
val () = out "PROBE7_BEGIN\n";
val n1 = mkNum 1; val n2 = twoC; val n3 = mkNum 3; val n4 = mkNum 4; val n6 = mkNum 6;
val n8 = mkNum 8; val n9 = mkNum 9; val n11 = mkNum 11; val n12 = mkNum 12; val n16 = mkNum 16;
val n18 = mkNum 18; val n24 = mkNum 24; val n33 = mkNum 33; val n36 = mkNum 36; val n54 = mkNum 54;
val n70 = mkNum 70; val n108 = mkNum 108;
fun pr name th = out (name ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n");
fun dbg name f = (let val r = f () in out (name ^ " OK\n"); r end) handle e => (out (name ^ " EXN : " ^ General.exnMessage e ^ "\n"); raise e);
fun ev2 (r,t) = t;
val mult_assoc_vBL = varify mult_assoc;
fun multassocBL (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtBL
        [(("m",0), ctermBL mt),(("n",0), ctermBL nt),(("k",0), ctermBL kt)] mult_assoc_vBL);
   (* oeq (mult (mult m n) k)(mult m (mult n k)) *)

fun lt_add_mono_lBL (Zt, Xt, Yt) hlt =
  let val base = le_add_mono_lBL (Zt, suc Xt, Yt) hlt
      val aSr = add_Sr_BL_at (Zt, Xt)
  in le_cong_lBL (add Zt (suc Xt), suc (add Zt Xt), add Zt Yt) aSr base end;

fun mult_lt_cancel_lBL (kt, Xt, Yt) hlt =
  let
    val hAss = Thm.assume (ctermBL (jT (le Yt Xt)))
    val mle = mult_le_monoBL (kt, Yt, Xt) hAss
    val le_S_self = le_transBL_at (suc (mult kt Xt), mult kt Yt, mult kt Xt) hlt mle
    val ff = lt_irreflBL_at (mult kt Xt) OF [le_S_self]
    val negYX = impI_BL (le Yt Xt, oFalseC) (Thm.implies_intr (ctermBL (jT (le Yt Xt))) ff)
  in nle_lt_BL (Yt, Xt) negYX end;

(* add_right_cancel *)
val add_left_cancel_vBL = varify add_left_cancel;
fun add_left_cancelBL (mt, at, bt) h =
  beta_norm (Drule.infer_instantiate ctxtBL
    [(("m",0), ctermBL mt),(("a",0), ctermBL at),(("b",0), ctermBL bt)] add_left_cancel_vBL) OF [h];
fun add_right_cancelBL (at, bt, kt) h =
  let val cmA = addcommBL_at (at, kt) val cmB = addcommBL_at (bt, kt)
      val h2 = oeqtransBL OF [oeqsymBL cmA, oeqtransBL OF [h, cmB]]
  in add_left_cancelBL (kt, at, bt) h2 end;

(* helper : oeq (mult cBig s)(add (mult cA s)(mult cB s)) for cBig = cA+cB (numerals) *)
fun split_mult (cBig, cA, cB) sF =
  let val eAB = ev2 (add_eval cA cB)   (* oeq (add cA cB) cBig *)
      val rd = rdistBL (cA, cB, sF)     (* oeq (mult (add cA cB) s)(add (mult cA s)(mult cB s)) *)
  in oeqtransBL OF [mult_cong_lBL (cBig, add cA cB, sF) (oeqsymBL eAB), rd] end;
   (* oeq (mult cBig s)(add (mult cA s)(mult cB s)) *)

(* ============================================================================
   E3 : le 36 s ==> lt (add (mult 33 s) 70)(mult s s)
   ============================================================================ *)
fun E3_of sF hLe36 =
  let
    val mle = mult_le_monoBL (sF, n36, sF) hLe36
    val cm = multcommBL_at (n36, sF)
    val le_36s_ss = le_cong_lBL (mult sF n36, mult n36 sF, mult sF sF) (oeqsymBL cm) mle
    val m36s_split = split_mult (n36, n33, n3) sF      (* oeq (mult 36 s)(add (mult 33 s)(mult 3 s)) *)
    val m3_le = mult_le_monoBL (n3, n36, sF) hLe36
    val e3_36 = ev2 (mult_eval n3 n36)
    val le_108_3s = le_cong_lBL (mult n3 n36, n108, mult n3 sF) e3_36 m3_le
    val lt70_108 = lt_evalBL 70 108
    val lt70_3s = le_transBL_at (suc n70, n108, mult n3 sF) lt70_108 le_108_3s
    val lt_sum = lt_add_mono_lBL (mult n33 sF, n70, mult n3 sF) lt70_3s
    val lt_sum2 = le_cong_rBL (suc (add (mult n33 sF) n70), add (mult n33 sF)(mult n3 sF), mult n36 sF)
          (oeqsymBL m36s_split) lt_sum
  in le_transBL_at (suc (add (mult n33 sF) n70), mult n36 sF, mult sF sF) lt_sum2 le_36s_ss end;

(* ============================================================================
   E1full : oeq (add (mult 3 (mult E s9)) 16)(add (mult 3 (mult s s))(add (mult 33 s) 70))
   ============================================================================ *)
fun mEs9_canon sF =   (* oeq (mult E s9)(add ss (add (mult 11 s) 18)) *)
  let
    val E = suc (suc sF); val s9 = add sF n9; val ss = mult sF sF; val m9s = mult sF n9
    val d0 = ldistBL (E, sF, n9)
    val a1 = multSucBL_at (suc sF, sF)
    val a2 = multSucBL_at (sF, sF)
    val mEs = oeqtransBL OF [a1, add_cong_rBL (sF, mult (suc sF) sF, add sF ss) a2]
    val b1 = multSucBL_at (suc sF, n9)
    val b2 = multSucBL_at (sF, n9)
    val mE9 = oeqtransBL OF [b1, add_cong_rBL (n9, mult (suc sF) n9, add n9 (mult sF n9)) b2]
    val raw = oeqtransBL OF [d0,
          oeqtransBL OF [add_cong_lBL (mult E sF, add sF (add sF ss), mult E n9) mEs,
                         add_cong_rBL (add sF (add sF ss), mult E n9, add n9 (add n9 m9s)) mE9]]
          (* oeq (mult E s9)(add P Q), P=add s (add s ss), Q=add 9 (add 9 m9s) *)
    val P = add sF (add sF ss); val Q = add n9 (add n9 m9s)
    (* P -> add ss (add s s) *)
    val P_eq = oeqtransBL OF [oeqsymBL (addassocBL (sF, sF, ss)), addcommBL_at (add sF sF, ss)]
    val step_ss = oeqtransBL OF [
          add_cong_lBL (P, add ss (add sF sF), Q) P_eq,            (* add P Q -> add (add ss (add s s)) Q *)
          addassocBL (ss, add sF sF, Q)]                           (* -> add ss (add (add s s) Q) *)
          (* oeq (add P Q)(add ss (add (add s s) Q)) *)
    (* inner : add (add s s) Q -> add (mult 11 s) 18.
       Q = add 9 (add 9 m9s) ; reassoc to add (add 9 9) m9s = add 18 m9s = add m9s 18 *)
    val q_a = oeqsymBL (addassocBL (n9, n9, m9s))     (* oeq (add 9 (add 9 m9s))(add (add 9 9) m9s) *)
    val e99 = ev2 (add_eval n9 n9)                    (* oeq (add 9 9) 18 *)
    val q_b = add_cong_lBL (add n9 n9, n18, m9s) e99  (* oeq (add (add 9 9) m9s)(add 18 m9s) *)
    val q_c = addcommBL_at (n18, m9s)                 (* oeq (add 18 m9s)(add m9s 18) *)
    val Q_eq = oeqtransBL OF [q_a, oeqtransBL OF [q_b, q_c]]   (* oeq Q (add m9s 18) *)
    (* add (add s s) Q -> add (add s s)(add m9s 18) -> add (add (add s s) m9s) 18 [assoc rev]
       -> add (mult 11 s) 18 [coeff] *)
    val coeff =
      let
        val c_s_a = mult1lBL sF
        val twoS = rdistBL (n1, n1, sF)
        val e11 = ev2 (add_eval n1 n1)
        val two_s_eq = oeqtransBL OF [mult_cong_lBL (n2, add n1 n1, sF) (oeqsymBL e11), twoS]
        val ss_to_2s = oeqtransBL OF [two_s_eq,
                         oeqtransBL OF [add_cong_lBL (mult n1 sF, sF, mult n1 sF) c_s_a,
                                        add_cong_rBL (sF, mult n1 sF, sF) c_s_a]]   (* oeq (mult 2 s)(add s s) *)
        val m11s_eq = split_mult (n11, n2, n9) sF      (* oeq (mult 11 s)(add (mult 2 s)(mult 9 s)) *)
        val m9s_eq = multcommBL_at (sF, n9)            (* oeq (mult s 9)(mult 9 s) *)
      in oeqtransBL OF [
            add_cong_lBL (add sF sF, mult n2 sF, m9s) (oeqsymBL ss_to_2s),
            oeqtransBL OF [add_cong_rBL (mult n2 sF, m9s, mult n9 sF) m9s_eq, oeqsymBL m11s_eq]]
      end   (* oeq (add (add s s) m9s)(mult 11 s) *)
    val inner = oeqtransBL OF [
          add_cong_rBL (add sF sF, Q, add m9s n18) Q_eq,               (* add (add s s) Q -> add (add s s)(add m9s 18) *)
          oeqtransBL OF [oeqsymBL (addassocBL (add sF sF, m9s, n18)),  (* -> add (add (add s s) m9s) 18 *)
                         add_cong_lBL (add (add sF sF) m9s, mult n11 sF, n18) coeff]]  (* -> add (mult 11 s) 18 *)
          (* oeq (add (add s s) Q)(add (mult 11 s) 18) *)
    val full = oeqtransBL OF [raw,
          oeqtransBL OF [step_ss, add_cong_rBL (ss, add (add sF sF) Q, add (mult n11 sF) n18) inner]]
          (* oeq (mult E s9)(add ss (add (mult 11 s) 18)) *)
  in full end;

fun E1_of sF =
  let
    val E = suc (suc sF); val s9 = add sF n9; val ss = mult sF sF
    val canon = mEs9_canon sF   (* oeq (mult E s9)(add ss (add (mult 11 s) 18)) *)
    (* mult 3 (mult E s9) = mult 3 (add ss (add 11s 18)) = add (mult 3 ss)(mult 3 (add 11s 18))
                          = add (mult 3 ss)(add (mult 3 (mult 11 s))(mult 3 18))
                          = add (mult 3 ss)(add (mult 33 s) 54) *)
    val c1 = mult_cong_rBL (n3, mult E s9, add ss (add (mult n11 sF) n18)) canon
             (* oeq (mult 3 (mult E s9))(mult 3 (add ss (add 11s 18))) *)
    val c2 = ldistBL (n3, ss, add (mult n11 sF) n18)
             (* oeq (mult 3 (add ss (add 11s 18)))(add (mult 3 ss)(mult 3 (add 11s 18))) *)
    val c3 = ldistBL (n3, mult n11 sF, n18)
             (* oeq (mult 3 (add 11s 18))(add (mult 3 (mult 11 s))(mult 3 18)) *)
    (* mult 3 (mult 11 s) = mult (mult 3 11) s = mult 33 s *)
    val ma = multassocBL (n3, n11, sF)       (* oeq (mult (mult 3 11) s)(mult 3 (mult 11 s)) *)
    val e311 = ev2 (mult_eval n3 n11)        (* oeq (mult 3 11) 33 *)
    val m33s = oeqtransBL OF [oeqsymBL ma, mult_cong_lBL (mult n3 n11, n33, sF) e311]
               (* oeq (mult 3 (mult 11 s))(mult 33 s) *)
    val e318 = ev2 (mult_eval n3 n18)        (* oeq (mult 3 18) 54 *)
    val c3b = oeqtransBL OF [c3, oeqtransBL OF [add_cong_lBL (mult n3 (mult n11 sF), mult n33 sF, mult n3 n18) m33s,
                                               add_cong_rBL (mult n33 sF, mult n3 n18, n54) e318]]
              (* oeq (mult 3 (add 11s 18))(add (mult 33 s) 54) *)
    val m3Es9 = oeqtransBL OF [c1, oeqtransBL OF [c2, add_cong_rBL (mult n3 ss, mult n3 (add (mult n11 sF) n18), add (mult n33 sF) n54) c3b]]
                (* oeq (mult 3 (mult E s9))(add (mult 3 ss)(add (mult 33 s) 54)) *)
    (* + 16 : add (mult 3 (mult E s9)) 16 = add (add (mult 3 ss)(add 33s 54)) 16
            = add (mult 3 ss)(add (add 33s 54) 16) = add (mult 3 ss)(add 33s (add 54 16))
            = add (mult 3 ss)(add 33s 70) *)
    val L0 = add_cong_lBL (mult n3 (mult E s9), add (mult n3 ss)(add (mult n33 sF) n54), n16) m3Es9
             (* oeq (add (mult 3 (mult E s9)) 16)(add (add (mult 3 ss)(add 33s 54)) 16) *)
    val L1 = addassocBL (mult n3 ss, add (mult n33 sF) n54, n16)
             (* oeq (...)(add (mult 3 ss)(add (add 33s 54) 16)) *)
    val L2 = addassocBL (mult n33 sF, n54, n16)   (* oeq (add (add 33s 54) 16)(add 33s (add 54 16)) *)
    val e5416 = ev2 (add_eval n54 n16)            (* oeq (add 54 16) 70 *)
    val L3 = oeqtransBL OF [L2, add_cong_rBL (mult n33 sF, add n54 n16, n70) e5416]
             (* oeq (add (add 33s 54) 16)(add 33s 70) *)
    val full = oeqtransBL OF [L0, oeqtransBL OF [L1, add_cong_rBL (mult n3 ss, add (add (mult n33 sF) n54) n16, add (mult n33 sF) n70) L3]]
               (* oeq (add (mult 3 (mult E s9)) 16)(add (mult 3 ss)(add 33s 70)) *)
  in full end;

(* ============================================================================
   Ppoly : le 36 s ==> lt (add (mult 3 (mult E s9)) 16)(mult 4 (mult s s))
   ============================================================================ *)
fun Ppoly_of sF hLe36 =
  let
    val E = suc (suc sF); val s9 = add sF n9; val ss = mult sF sF
    val E1 = E1_of sF                          (* oeq (add (mult 3 (mult E s9)) 16)(add (mult 3 ss)(add 33s 70)) *)
    val E2 = split_mult (n4, n3, n1) ss        (* oeq (mult 4 ss)(add (mult 3 ss)(mult 1 ss)) *)
    val m1ss = mult1lBL ss                      (* oeq (mult 1 ss) ss *)
    val E2b = oeqtransBL OF [E2, add_cong_rBL (mult n3 ss, mult n1 ss, ss) m1ss]
              (* oeq (mult 4 ss)(add (mult 3 ss) ss) *)
    val e3 = E3_of sF hLe36                     (* lt (add 33s 70) ss *)
    val ltadd = lt_add_mono_lBL (mult n3 ss, add (mult n33 sF) n70, ss) e3
                (* lt (add (mult 3 ss)(add 33s 70))(add (mult 3 ss) ss) *)
    (* ltadd is a lt : its LHS is Suc(add (3ss)(33s+70)).  rewrite that Suc(..) via Suc_cong on (E1 sym). *)
    val g1 = le_cong_lBL (suc (add (mult n3 ss)(add (mult n33 sF) n70)), suc (add (mult n3 (mult E s9)) n16), add (mult n3 ss) ss)
             (Suc_congBL OF [oeqsymBL E1]) ltadd
             (* lt (add (mult 3 (mult E s9)) 16)(add (mult 3 ss) ss) *)
    val g2 = le_cong_rBL (suc (add (mult n3 (mult E s9)) n16), add (mult n3 ss) ss, mult n4 ss)
             (oeqsymBL E2b) g1
             (* lt (add (mult 3 (mult E s9)) 16)(mult 4 ss) *)
  in g2 end;

val () = out "P7BODY_DONE\n";

(* ============================================================================
   PROBE 8 : POLY bounds A, B' + final assembly -> poly_ineq.
   Requires : Ppoly_of (fun), split_mult, multassocBL, lt_add_mono_lBL,
              mult_lt_cancel_lBL, add_right_cancelBL, all live (probe7 body).
   ============================================================================ *)
val () = out "PROBE8_BEGIN\n";
val nn1 = mkNum 1;
fun pr name th = out (name ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n");

val lt0_4 = lt_evalBL 0 4;
val lt0_3 = lt_evalBL 0 3;

(* le_add_cancel_l : le (add k a)(add k b) ==> le a b *)
fun le_add_cancel_lBL (kt, at, bt) h =
  let
    val goalC = le at bt
    val Pw = Abs("w_lac", natT, oeq (add kt bt)(add (add kt at)(Bound 0)))
    fun body wF (hw : thm) =   (* hw : oeq (add k b)(add (add k a) w) *)
      let
        val asc = addassocBL (kt, at, wF)          (* oeq (add (add k a) w)(add k (add a w)) *)
        val h2 = oeqtransBL OF [hw, asc]            (* oeq (add k b)(add k (add a w)) *)
        val canc = add_left_cancelBL (kt, bt, add at wF) h2   (* oeq b (add a w) *)
      in le_introBL (at, bt, wF) canc end
  in exE_elimBL (Pw, goalC) h "w_lacx" body end;
(* le_add_cancel_r : le (add a k)(add b k) ==> le a b  (via comm) *)
fun le_add_cancel_rBL (at, bt, kt) h =
  let
    val cmA = addcommBL_at (at, kt)   (* oeq (add a k)(add k a) *)
    val cmB = addcommBL_at (bt, kt)   (* oeq (add b k)(add k b) *)
    val h1 = le_cong_lBL (add at kt, add kt at, add bt kt) cmA h    (* le (add k a)(add b k) *)
    val h2 = le_cong_rBL (add kt at, add bt kt, add kt bt) cmB h1   (* le (add k a)(add k b) *)
  in le_add_cancel_lBL (kt, at, bt) h2 end;

(* ---- Bound A : le (mult 12 (mult E b))(mult 3 (mult E s9)) ---- *)
fun boundA_of sF =
  let
    val E = suc (suc sF); val s9 = add sF n9; val b = rdiv s9 n4
    (* 4b <= s9 : div_mod s9 = add (mult 4 b) r ; le (mult 4 b)(add (mult 4 b) r) = le (mult 4 b) s9 *)
    val dme = div_mod_eqBL (s9, n4) lt0_4        (* oeq s9 (add (mult 4 b)(rmod s9 4)) *)
    val r = rmod s9 n4
    val le4b_s9 = le_cong_rBL (mult n4 b, add (mult n4 b) r, s9) (oeqsymBL dme) (le_addBL_at (mult n4 b, r))
                  (* le (mult 4 b) s9 *)
    (* mult E (mult 4 b) <= mult E s9 [mono prefix E] ; mult 3 (...) <= mult 3 (...) [mono prefix 3] *)
    val mE = mult_le_monoBL (E, mult n4 b, s9) le4b_s9         (* le (mult E (mult 4 b))(mult E s9) *)
    val m3E = mult_le_monoBL (n3, mult E (mult n4 b), mult E s9) mE   (* le (mult 3 (mult E (mult 4 b)))(mult 3 (mult E s9)) *)
    (* mult 12 (mult E b) = mult 3 (mult E (mult 4 b)) :
       mult 12 (mult E b) = mult (mult 3 4)(mult E b) [12 = 3*4] = mult 3 (mult 4 (mult E b)) [assoc]
       ; mult 4 (mult E b) = mult E (mult 4 b) [comm/assoc] *)
    val e12 = #2 (mult_eval n3 n4)               (* oeq (mult 3 4) 12 *)
    val asc1 = multassocBL (n3, n4, mult E b)    (* oeq (mult (mult 3 4)(mult E b))(mult 3 (mult 4 (mult E b))) *)
    val m12_eq1 = oeqtransBL OF [mult_cong_lBL (n12, mult n3 n4, mult E b) (oeqsymBL e12), asc1]
                  (* oeq (mult 12 (mult E b))(mult 3 (mult 4 (mult E b))) *)
    (* mult 4 (mult E b) = mult E (mult 4 b) : 4*(E*b) = (4*E)*b = (E*4)*b = E*(4*b) *)
    val x1 = oeqsymBL (multassocBL (n4, E, b))   (* oeq (mult 4 (mult E b))(mult (mult 4 E) b) *)
    val x2 = mult_cong_lBL (mult n4 E, mult E n4, b) (multcommBL_at (n4, E))   (* oeq (mult (mult 4 E) b)(mult (mult E 4) b) *)
    val x3 = multassocBL (E, n4, b)              (* oeq (mult (mult E 4) b)(mult E (mult 4 b)) *)
    val m4Eb_eq = oeqtransBL OF [x1, oeqtransBL OF [x2, x3]]   (* oeq (mult 4 (mult E b))(mult E (mult 4 b)) *)
    val m12_eq = oeqtransBL OF [m12_eq1, mult_cong_rBL (n3, mult n4 (mult E b), mult E (mult n4 b)) m4Eb_eq]
                 (* oeq (mult 12 (mult E b))(mult 3 (mult E (mult 4 b))) *)
    val g = le_cong_lBL (mult n3 (mult E (mult n4 b)), mult n12 (mult E b), mult n3 (mult E s9)) (oeqsymBL m12_eq) m3E
            (* le (mult 12 (mult E b))(mult 3 (mult E s9)) *)
  in g end;

val () =
  (let val sF = Free("s_ba", natT) in pr "boundA" (boundA_of sF) end)
  handle e => out ("boundA EXN : " ^ General.exnMessage e ^ "\n");
val () = out "BOUNDA_DONE\n";

(* ---- Bound B' : le (mult s s)(add n n) ==> le (mult 4 (mult s s))(add (mult 24 D3) 16) ---- *)
fun boundB_of sF nF hSq =   (* hSq : le (mult s s)(add n n) *)
  let
    val ss = mult sF sF; val D3 = rdiv nF n3
    (* mult 4 ss <= mult 4 (add n n) [mono prefix 4] *)
    val le_4ss = mult_le_monoBL (n4, ss, add nF nF) hSq   (* le (mult 4 ss)(mult 4 (add n n)) *)
    (* mult 4 (add n n) = add (mult 4 n)(mult 4 n) [ldist] = mult 8 n [8=4+4] *)
    val ld = ldistBL (n4, nF, nF)                (* oeq (mult 4 (add n n))(add (mult 4 n)(mult 4 n)) *)
    val m8n_split = split_mult (n8, n4, n4) nF   (* oeq (mult 8 n)(add (mult 4 n)(mult 4 n)) *)
    val m4nn_eq = oeqtransBL OF [ld, oeqsymBL m8n_split]   (* oeq (mult 4 (add n n))(mult 8 n) *)
    val le_4ss_8n = le_cong_rBL (mult n4 ss, mult n4 (add nF nF), mult n8 nF) m4nn_eq le_4ss   (* le (mult 4 ss)(mult 8 n) *)
    (* mult 8 n <= add (mult 24 D3) 16 :
       div_mod n = add (mult 3 D3) r3 ; mult 8 n = mult 8 (add (mult 3 D3) r3)
         = add (mult 8 (mult 3 D3))(mult 8 r3) [ldist] = add (mult 24 D3)(mult 8 r3) [assoc 8*3=24]
       ; r3 <= 2 -> mult 8 r3 <= mult 8 2 = 16 *)
    val dme_n = div_mod_eqBL (nF, n3) lt0_3      (* oeq n (add (mult 3 D3)(rmod n 3)) *)
    val r3 = rmod nF n3
    val m8n_a = mult_cong_rBL (n8, nF, add (mult n3 D3) r3) dme_n   (* oeq (mult 8 n)(mult 8 (add (mult 3 D3) r3)) *)
    val m8n_b = ldistBL (n8, mult n3 D3, r3)     (* oeq (mult 8 (add (mult 3 D3) r3))(add (mult 8 (mult 3 D3))(mult 8 r3)) *)
    (* mult 8 (mult 3 D3) = mult (mult 8 3) D3 = mult 24 D3 *)
    val asc = multassocBL (n8, n3, D3)           (* oeq (mult (mult 8 3) D3)(mult 8 (mult 3 D3)) *)
    val e83 = #2 (mult_eval n8 n3)               (* oeq (mult 8 3) 24 *)
    val m24 = oeqtransBL OF [oeqsymBL asc, mult_cong_lBL (mult n8 n3, n24, D3) e83]   (* oeq (mult 8 (mult 3 D3))(mult 24 D3) *)
    val m8n_eq = oeqtransBL OF [m8n_a, oeqtransBL OF [m8n_b, add_cong_lBL (mult n8 (mult n3 D3), mult n24 D3, mult n8 r3) m24]]
                 (* oeq (mult 8 n)(add (mult 24 D3)(mult 8 r3)) *)
    (* r3 <= 2 : lt r3 3 -> le r3 2 *)
    val r3_le2 = le_suc_inv_BL (r3, n2) (rmod_ltBL (nF, n3) lt0_3)   (* le r3 2 *)
    val le_8r3 = mult_le_monoBL (n8, r3, n2) r3_le2   (* le (mult 8 r3)(mult 8 2) *)
    val e82 = #2 (mult_eval n8 n2)               (* oeq (mult 8 2) 16 *)
    val le_8r3_16 = le_cong_rBL (mult n8 r3, mult n8 n2, n16) e82 le_8r3   (* le (mult 8 r3) 16 *)
    (* le (add (mult 24 D3)(mult 8 r3))(add (mult 24 D3) 16) [le_add_mono_l fix 24 D3] *)
    val le_sum = le_add_mono_lBL (mult n24 D3, mult n8 r3, n16) le_8r3_16   (* le (add (24 D3)(8 r3))(add (24 D3) 16) *)
    val le_8n_24 = le_cong_lBL (add (mult n24 D3)(mult n8 r3), mult n8 nF, add (mult n24 D3) n16) (oeqsymBL m8n_eq) le_sum
                   (* le (mult 8 n)(add (mult 24 D3) 16) *)
    val g = le_transBL_at (mult n4 ss, mult n8 nF, add (mult n24 D3) n16) le_4ss_8n le_8n_24
            (* le (mult 4 ss)(add (mult 24 D3) 16) *)
  in g end;

val () =
  (let val sF = Free("s_bb", natT) val nF = Free("n_bb", natT)
       val h = Thm.assume (ctermBL (jT (le (mult sF sF)(add nF nF))))
   in pr "boundB" (boundB_of sF nF h) end)
  handle e => out ("boundB EXN : " ^ General.exnMessage e ^ "\n");
val () = out "BOUNDB_DONE\n";

(* ---- final assembly : poly_ineq ---- *)
fun poly_ineq_body sF nF hLe36 hSq =
  let
    val E = suc (suc sF); val s9 = add sF n9; val b = rdiv s9 n4
    val ss = mult sF sF; val D3 = rdiv nF n3
    val Ppoly = Ppoly_of sF hLe36        (* lt (add (mult 3 (mult E s9)) 16)(mult 4 ss) = le (Suc(add (3Es9) 16))(mult 4 ss) *)
    val Bp = boundB_of sF nF hSq         (* le (mult 4 ss)(add (mult 24 D3) 16) *)
    val A  = boundA_of sF                (* le (mult 12 (mult E b))(mult 3 (mult E s9)) *)
    (* chain Ppoly + Bp : le (Suc(add (3Es9) 16))(add (mult 24 D3) 16) *)
    val ch1 = le_transBL_at (suc (add (mult n3 (mult E s9)) n16), mult n4 ss, add (mult n24 D3) n16) Ppoly Bp
              (* le (Suc(add (3Es9) 16))(add (24 D3) 16) *)
    (* Suc(add X 16) = add (Suc X) 16 [add_Suc sym] ; X = mult 3 (mult E s9) *)
    val sucAdd = oeqsymBL (addSucBL_at (mult n3 (mult E s9), n16))   (* oeq (Suc(add X 16))(add (Suc X) 16) *)
    val ch2 = le_cong_lBL (suc (add (mult n3 (mult E s9)) n16), add (suc (mult n3 (mult E s9))) n16, add (mult n24 D3) n16) sucAdd ch1
              (* le (add (Suc X) 16)(add (24 D3) 16) *)
    val ch3 = le_add_cancel_rBL (suc (mult n3 (mult E s9)), mult n24 D3, n16) ch2   (* le (Suc X)(mult 24 D3) *)
    (* A -> le (Suc(mult 12 (mult E b)))(Suc(mult 3 (mult E s9))) -> trans ch3 *)
    val sucA = le_suc_monoBL_at (mult n12 (mult E b), mult n3 (mult E s9)) A   (* le (Suc(12 E b))(Suc(3 E s9)) *)
    val lt12 = le_transBL_at (suc (mult n12 (mult E b)), suc (mult n3 (mult E s9)), mult n24 D3) sucA ch3
               (* le (Suc(12 E b))(mult 24 D3) = lt (mult 12 (mult E b))(mult 24 D3) *)
    (* mult 24 D3 = mult 12 (mult 2 D3) : 24 = 12*2 ; assoc *)
    val e24 = #2 (mult_eval n12 n2)              (* oeq (mult 12 2) 24 *)
    val asc24 = multassocBL (n12, n2, D3)        (* oeq (mult (mult 12 2) D3)(mult 12 (mult 2 D3)) *)
    val m24_eq = oeqtransBL OF [mult_cong_lBL (n24, mult n12 n2, D3) (oeqsymBL e24), asc24]
                 (* oeq (mult 24 D3)(mult 12 (mult 2 D3)) *)
    val lt12b = le_cong_rBL (suc (mult n12 (mult E b)), mult n24 D3, mult n12 (mult n2 D3)) m24_eq lt12
                (* lt (mult 12 (mult E b))(mult 12 (mult 2 D3)) *)
    (* cancel 12 *)
    val g = mult_lt_cancel_lBL (n12, mult E b, mult n2 D3) lt12b   (* lt (mult E b)(mult 2 D3) *)
  in g end;

val poly_ineq =
  (let
     val sF = Free("s_pi", natT) val nF = Free("n_pi", natT)
     val h36 = Thm.assume (ctermBL (jT (le n36 sF)))
     val hSq = Thm.assume (ctermBL (jT (le (mult sF sF)(add nF nF))))
     val body = poly_ineq_body sF nF h36 hSq
     val d2 = Thm.implies_intr (ctermBL (jT (le (mult sF sF)(add nF nF)))) body
     val d1 = Thm.implies_intr (ctermBL (jT (le n36 sF))) d2
   in SOME (varify d1) end)
  handle e => (out ("poly_ineq EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val () = (case poly_ineq of
    SOME th => out ("poly_ineq 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
  | NONE => out "poly_ineq NONE\n");
val poly_ineq_ok = (case poly_ineq of SOME th => zhBL th | NONE => false);
val () = if poly_ineq_ok then out "POLY_INEQ_OK\n" else out "POLY_INEQ_FAIL\n";

val () = out "PROBE8_DONE\n";

(* ============================================================================
   PROBE 9 : crude_tail assembly from POW (pow_bound) + POLY (poly_ineq) +
   seb_reduce + seb_tail_reduce (banked).  S0 = 36.
     crude_tail : le 36 s ==> le (mult s s)(add n n) ==> lt (add n n)(mult (Suc s)(Suc s))
        ==> lt (mult (Suc (add n n))(pow (add n n)(Suc s)))(pow 4 (rdiv n 3))
   ============================================================================ *)
val () = out "PROBE9_BEGIN\n";
val fourC = suc (suc (suc (suc ZeroC)));
val cc36 = mkNum 36; val cc3 = mkNum 3; val cc9 = mkNum 9; val cc4 = mkNum 4;

(* instantiators for pow_bound and poly_ineq *)
val pow_bound_thm = (case pow_bound of SOME th => th | NONE => raise Fail "pow_bound NONE");
val poly_ineq_thm = (case poly_ineq of SOME th => th | NONE => raise Fail "poly_ineq NONE");
val pb_vars = Term.add_vars (Thm.prop_of pow_bound_thm) [];
val () = out ("pow_bound vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) pb_vars) ^ "\n");
val pi_vars = Term.add_vars (Thm.prop_of poly_ineq_thm) [];
val () = out ("poly_ineq vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) pi_vars) ^ "\n");
(* pow_bound : single var (s). poly_ineq : two vars (s, n). instantiate by name suffix *)
fun pow_bound_at sT h36 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL (map (fn (ix,_) => (ix, ctermBL sT)) pb_vars) pow_bound_thm)
  in Thm.implies_elim inst h36 end;
fun poly_ineq_at (sT, nT) h36 hSq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL
        (map (fn (ix as (nm,_),_) => if nm = "s_pi" then (ix, ctermBL sT) else (ix, ctermBL nT)) pi_vars) poly_ineq_thm)
  in Thm.implies_elim (Thm.implies_elim inst h36) hSq end;

(* crude_tail *)
val crude_tail =
  (let
     val sF = Free("s_ct2", natT) val nF = Free("n_ct2", natT)
     val twoN = add nF nF
     val K = mult (suc sF)(suc sF)
     val b = rdiv (add sF cc9) cc4
     val DT = rdiv nF cc3
     val h36 = Thm.assume (ctermBL (jT (le cc36 sF)))
     val hSq = Thm.assume (ctermBL (jT (le (mult sF sF) twoN)))
     val hSsq = Thm.assume (ctermBL (jT (lt twoN K)))
     (* seb_reduce : le (mult (Suc 2n)(pow 2n (Suc s)))(pow K (Suc(Suc s))) *)
     val sr = seb_reduce (sF, nF) hSsq
     (* pow_bound : le K (pow 2 b) *)
     val leK_2b = pow_bound_at sF h36
     (* poly_ineq : lt (mult (Suc(Suc s)) b)(mult 2 D) *)
     val hPoly = poly_ineq_at (sF, nF) h36 hSq
     (* seb_tail_reduce : lt (pow K (Suc(Suc s)))(pow 4 D) *)
     val tr = seb_tail_reduce (sF, b, DT) leK_2b hPoly
     val LHS = mult (suc twoN)(pow twoN (suc sF))
     val g = le_transBL_at (suc LHS, suc (pow K (suc (suc sF))), pow fourC DT)
               (le_suc_monoBL_at (LHS, pow K (suc (suc sF))) sr) tr
     val d3 = Thm.implies_intr (ctermBL (jT (lt twoN K))) g
     val d2 = Thm.implies_intr (ctermBL (jT (le (mult sF sF) twoN))) d3
     val d1 = Thm.implies_intr (ctermBL (jT (le cc36 sF))) d2
   in SOME (varify d1) end)
  handle e => (out ("crude_tail EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val () = (case crude_tail of
    SOME th => out ("crude_tail 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
  | NONE => out "crude_tail NONE\n");
val crude_tail_ok = (case crude_tail of SOME th => zhBL th | NONE => false);
val () = if crude_tail_ok then out "CRUDE_TAIL_OK\n" else out "CRUDE_TAIL_FAIL\n";

(* intended-form aconv check (mod stated premises) *)
val crude_tail_aconv =
  (case crude_tail of
     SOME th =>
       let
         val sV = Free("sCK", natT) val nV = Free("nCK", natT)
         val twoN = add nV nV val K = mult (suc sV)(suc sV)
         val intended =
           Logic.mk_implies (jT (le cc36 sV),
             Logic.mk_implies (jT (le (mult sV sV) twoN),
               Logic.mk_implies (jT (lt twoN K),
                 jT (lt (mult (suc twoN)(pow twoN (suc sV)))(pow fourC (rdiv nV cc3))))))
         val vs = Term.add_vars (Thm.prop_of th) []
         val inst = beta_norm (Drule.infer_instantiate ctxtBL
            (map (fn (ix as (nm,_),_) => if nm = "s_ct2" then (ix, ctermBL sV) else (ix, ctermBL nV)) vs) th)
       in (Thm.prop_of inst) aconv intended end
   | NONE => false);
val () = out ("crude_tail aconv intended = " ^ Bool.toString crude_tail_aconv ^ "\n");
val () = if crude_tail_ok andalso crude_tail_aconv then out "CRUDE_TAIL_PROVED S0=36\n" else out "CRUDE_TAIL_PROVED_FAIL\n";

(* ---- axiom audit ---- *)
val () =
  let
    val thy = Proof_Context.theory_of ctxtBL
    val names = map fst (Theory.all_axioms_of thy)
    val hasEM = List.exists (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names
    val nClassical = length (List.filter (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names)
    val bitlenAx = List.filter (fn s => String.isSubstring "bitlen" s) names
    val suspicious = List.filter (fn s =>
         String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s
         orelse String.isSubstring "chebyshev" s orelse String.isSubstring "postulate" s
         orelse String.isSubstring "seb" s orelse String.isSubstring "threshold" s
         orelse String.isSubstring "window" s orelse String.isSubstring "crude" s
         orelse String.isSubstring "pow_bound" s orelse String.isSubstring "poly_ineq" s
         orelse String.isSubstring "inequality" s) names
  in out ("CRUDE_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " ex_middle_present=" ^ Bool.toString hasEM
          ^ " classical_count=" ^ Int.toString nClassical
          ^ " bitlen_axioms=" ^ Int.toString (length bitlenAx)
          ^ " suspicious_count=" ^ Int.toString (length suspicious) ^ "\n");
     app (fn s => out ("  SUSPICIOUS AXIOM: " ^ s ^ "\n")) suspicious
  end;

val () = out "PROBE9_DONE\n";
val () = out "W1_POW_POLY_DELTA_DONE\n";
