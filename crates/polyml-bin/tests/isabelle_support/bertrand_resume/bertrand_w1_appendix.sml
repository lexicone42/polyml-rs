
(* ============================================================================
   BERTRAND W1 — the analytic threshold (the LAST wall).
   APPENDIX to bertrand_f7_full.sml.  Final base context: ctxtV4/ctermV4/thyV4.

   Goal (the hard large-n half):
     bertrand_large : le N0 n ==> Ex p. prime2 p /\ lt n p /\ le p (add n n)
   proved by contradiction from the banked threshold_assembled:
     4^n <= (2n+1)*(2n)^(s+1)*4^(2n/3)     [s = floor_sqrt(2n), guard le s (2n/3)]
   plus the sub-exponential bound (SEB):
     4^(n/3) > (2n+1)*(2n)^(s+1)           [for n >= N0]

   Stages (each GATED on an aconv / 0-hyp check):
     (DIV) the divide / multiply-back reduction : IF  lt ((2n+1)*(2n)^(s+1)) (4^(n/3))
           THEN threshold_assembled's RHS < 4^n, contradicting 4^n <= RHS.
           [marker SUFFICES_OK]
     (SEB) 4^(n/3) > (2n+1)*(2n)^(s+1) for n >= N0.   [marker SEB_OK]
     (TH)  threshold contradiction : H + n>=N0 => oFalse.  [marker THRESHOLD_OK]
     (BL)  bertrand_large.  [marker BERTRAND_LARGE_OK]

   Soundness: bertrand_large (if closed) must be 0-hyp + aconv the intended term;
   the only classical axiom is ex_middle; NO new const with a non-conservative
   defining axiom; NEVER assert a result as an axiom.
   ============================================================================ *)
val () = (Proofterm.proofs := 0);   (* bound RAM; the kernel still type-checks every inference *)
val () = out "W1_APPENDIX_BEGIN\n";

(* convenient abbreviations on the final context *)
val three4 = suc (suc (suc ZeroC));   (* 3 *)
val one4   = suc ZeroC;               (* 1 *)

(* ----------------------------------------------------------------------------
   rdiv-self bound on V4 :  le (mult 3 (rdiv N 3)) N   [3*(N/3) <= N]
   (the V4 mirror of pmNp_le_N3 ; div_mod_eq + le_add + cong.)
   ---------------------------------------------------------------------------- *)
val lt0_3_w1 = le_suc_mono4_at (ZeroC, suc (suc ZeroC)) (le_zero4_at (suc (suc ZeroC)));  (* le 1 3 = lt 0 3 *)
val lt0_4 = le_suc_mono4_at (ZeroC, suc (suc (suc ZeroC))) (le_zero4_at (suc (suc (suc ZeroC))));  (* le 1 4 = lt 0 4 *)

fun three_mul_div_le N =
  let
    val divEq = div_mod_eq_4 (N, three4) lt0_3_w1   (* oeq N (add (mult 3 (rdiv N 3)) (rmod N 3)) *)
    val Q = mult three4 (rdiv N three4)
    val le0 = le_add4_at (Q, rmod N three4)          (* le Q (add Q (rmod N 3)) *)
    val g = le_cong_r4 (Q, add Q (rmod N three4), N) (oeq_sym OF [divEq]) le0
  in g end;   (* le (mult 3 (rdiv N 3)) N *)

val () = out ("three_mul_div_le smoke : "
  ^ Syntax.string_of_term ctxtV4 (Thm.prop_of (three_mul_div_le (Free("N_w1",natT)))) ^ "\n");

(* ----------------------------------------------------------------------------
   rdiv split sum bound :  le (add (rdiv n 3) (rdiv (2n) 3)) n
   Proof : 3*(n/3) <= n  and  3*(2n/3) <= 2n  [three_mul_div_le].
           So  3*(n/3) + 3*(2n/3) <= n + 2n = 3n.
           3*(n/3 + 2n/3) = 3*(n/3) + 3*(2n/3)  [left_distrib].
           Hence  3*(n/3 + 2n/3) <= 3n,  and by 3-cancellation  n/3 + 2n/3 <= n.
   We avoid a generic mult-cancel by working with le on the 3*-multiplied form
   and then dividing : actually we need a cancellation le (3a)(3b) ==> le a b.
   We derive that cancellation here (mult_le_cancel3).
   ---------------------------------------------------------------------------- *)

(* mult_le_cancel3 : le (mult 3 a)(mult 3 b) ==> le a b.
   Contrapositive-free direct route : le (3a)(3b) means 3b = 3a + w.
   We instead use: from le (3a)(3b), if not le a b then lt b a, i.e. le (Suc b) a,
   then mult_le_mono gives le (3*(Suc b))(3*a) = le (3b+3)(3a), contradicting le (3a)(3b)
   with 3a <= 3b < 3b+3 <= 3a — needs lt_irrefl.  Use le_total to case-split. *)
fun mult_le_cancel3 (aT, bT) h3 =   (* h3 : le (mult 3 a)(mult 3 b) -> le a b *)
  let
    (* case-split le a b  vs  le (Suc b) a (= lt b a) via le_total + le_eq_or_succ_le *)
    val tot = le_total_4 (aT, bT)   (* Disj (le a b)(le b a) *)
    (* caseA : le a b -> done *)
    val hA = Thm.assume (ctermV4 (jT (le aT bT)))
    val caseA = Thm.implies_intr (ctermV4 (jT (le aT bT))) hA
    (* caseB : le b a -> derive le a b too (then disjE both branches give le a b).
       le b a : either a=b (so le a b by le from oeq) or lt b a.
       le_eq_or_succ_le : le b a -> Disj (oeq b a)(le (Suc b) a). *)
    val hB = Thm.assume (ctermV4 (jT (le bT aT)))
    val splitB = le_eq_or_succ_le_4 (bT, aT) hB   (* Disj (oeq b a)(le (Suc b) a) *)
    (* caseB1 : oeq b a -> le a b (le_refl rewritten) *)
    val hB1 = Thm.assume (ctermV4 (jT (oeq bT aT)))
    val leB1 = le_cong_l4 (bT, aT, bT) hB1 (le_refl4_at bT)   (* le a b : from le b b and b=a on the left *)
    val caseB1 = Thm.implies_intr (ctermV4 (jT (oeq bT aT))) leB1
    (* caseB2 : le (Suc b) a -> contradiction with h3 -> le a b via oFalse *)
    val hB2 = Thm.assume (ctermV4 (jT (le (suc bT) aT)))   (* lt b a *)
    (* 3*(Suc b) <= 3*a  [mult_le_mono] *)
    val m1 = mult_le_mono_4 (three4, suc bT, aT) hB2   (* le (mult 3 (Suc b))(mult 3 a) *)
    (* mult 3 (Suc b) = add 3 (mult 3 b)  [mult_Suc_right] *)
    val mSr = beta_norm (Drule.infer_instantiate ctxtV4 [(("n",0),ctermV4 three4),(("m",0),ctermV4 bT)] mult_Suc_right_v4_)
              (* oeq (mult 3 (Suc b))(add 3 (mult 3 b)) *)
    (* so le (add 3 (mult 3 b))(mult 3 a) *)
    val m2 = le_cong_l4 (mult three4 (suc bT), add three4 (mult three4 bT), mult three4 aT) mSr m1
             (* le (add 3 (mult 3 b))(mult 3 a) *)
    (* combine with h3 : le (mult 3 a)(mult 3 b) -> le (add 3 (mult 3 b))(mult 3 b) [trans] *)
    val m3 = le_trans4_at (add three4 (mult three4 bT), mult three4 aT, mult three4 bT) m2 h3
             (* le (add 3 (mult 3 b))(mult 3 b) *)
    (* add 3 (mult 3 b) = add (mult 3 b) 3 [comm] ; so le (add (mult 3 b) 3)(mult 3 b) *)
    val cm = addcomm4_at (three4, mult three4 bT)   (* oeq (add 3 (mult 3 b))(add (mult 3 b) 3) *)
    val m4 = le_cong_l4 (add three4 (mult three4 bT), add (mult three4 bT) three4, mult three4 bT) cm m3
             (* le (add (mult 3 b) 3)(mult 3 b) *)
    (* but le (mult 3 b)(add (mult 3 b) 3) [le_add] ; trans -> le (add (mult 3 b) 3)(add (mult 3 b) 3)? no.
       We want contradiction : (mult 3 b) + 3 <= mult 3 b  is impossible.  Use lt:
       le (Suc (mult 3 b))(add (mult 3 b) 3)  [since 3 = Suc(Suc(Suc 0)), add (mult 3 b) 3 = Suc(...)] then trans with m4 gives lt (mult 3 b)(mult 3 b). *)
    (* le (Suc (mult 3 b))(add (mult 3 b) 3) : add (mult 3 b) 3 = Suc(add (mult 3 b) 2) [add_Suc_right], and le (Suc X)(Suc Y) <= le X Y with X=mult3b, Y = add (mult3b) 2.
       Simpler : le (mult 3 b)+1 <= (mult 3 b)+3.  le_add_mono on the constant tail.
       Build : lt (mult 3 b)(add (mult 3 b) 3) = le (Suc(mult 3 b))(add (mult 3 b) 3).
       add (mult 3 b) 3 = Suc(Suc(Suc(mult 3 b)))? No, 3 is on the right: add X 3 = add X (Suc(Suc(Suc 0))).
       Use: le (Suc X)(add X 3): X+3 = Suc(X+2) [add_Suc_right]; le (Suc X)(Suc(X+2)) <= le X (X+2) [le_suc_mono];
            le X (X+2) [le_add]. *)
    val X = mult three4 bT
    val Xp2 = add X (suc (suc ZeroC))   (* X + 2 *)
    val aSr3 = add_Sr4_at (X, suc (suc ZeroC))   (* oeq (add X (Suc 2))(Suc(add X 2)) = oeq (add X 3)(Suc(X+2)) *)
    val leXXp2 = le_add4_at (X, suc (suc ZeroC))   (* le X (add X 2) *)
    val leSXSXp2 = le_suc_mono4_at (X, Xp2) leXXp2  (* le (Suc X)(Suc(X+2)) *)
    val ltXX3 = le_cong_r4 (suc X, suc Xp2, add X three4) (oeq_sym OF [aSr3]) leSXSXp2
                (* le (Suc X)(add X 3) = lt X (add X 3) *)
    (* now lt X (add X 3) [ltXX3] and le (add X 3) X [m4] -> le (Suc X) X = lt X X -> oFalse *)
    val ltXX = le_trans4_at (suc X, add X three4, X) ltXX3 m4   (* le (Suc X) X = lt X X *)
    val falseB2 = lt_irrefl4_at X OF [ltXX]   (* oFalse *)
    val leB2 = oFalse_elim_4 (le aT bT) OF [falseB2]   (* le a b from oFalse *)
    val caseB2 = Thm.implies_intr (ctermV4 (jT (le (suc bT) aT))) leB2
    (* disjE on splitB : caseB1, caseB2 -> le a b under hB *)
    val leUnderB = disjE_4 (oeq bT aT, le (suc bT) aT, le aT bT) splitB caseB1 caseB2
    val caseB = Thm.implies_intr (ctermV4 (jT (le bT aT))) leUnderB
  in disjE_4 (le aT bT, le bT aT, le aT bT) tot caseA caseB end;

val () =
  let val aF = Free("a_mlc",natT) val bF = Free("b_mlc",natT)
      val h = Thm.assume (ctermV4 (jT (le (mult three4 aF)(mult three4 bF))))
      val th = mult_le_cancel3 (aF, bF) h
  in out ("mult_le_cancel3 smoke : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of th) ^ "\n") end;

(* ----------------------------------------------------------------------------
   div_sum_le_n :  le (add (rdiv n 3)(rdiv (add n n) 3)) n
   ---------------------------------------------------------------------------- *)
fun div_sum_le_n nT =
  let
    val twoN = add nT nT
    val a = rdiv nT three4
    val b = rdiv twoN three4
    (* 3*(n/3) <= n, 3*(2n/3) <= 2n *)
    val le1 = three_mul_div_le nT      (* le (mult 3 (n/3)) n *)
    val le2 = three_mul_div_le twoN    (* le (mult 3 (2n/3)) (2n) *)
    (* le (mult 3 a + mult 3 b)(n + 2n) via le_add_mono twice (mono on both args) *)
    (* le_add_mono_4 (x,y,c) : le x y -> le (add x c)(add y c) ; do 1st arg then 2nd *)
    val s1 = le_add_mono_4 (mult three4 a, nT, mult three4 b) le1   (* le (mult3a + mult3b)(n + mult3b) *)
    (* 2nd arg : le (mult 3 b) (2n) -> le (n + mult3b)(n + 2n) ; commute to use le_add_mono *)
    val s2raw = le_add_mono_4 (mult three4 b, twoN, nT) le2   (* le (mult3b + n)(2n + n) *)
    (* convert s2raw to (n + mult3b) <= (n + 2n) *)
    val s2a = le_cong_l4 (add (mult three4 b) nT, add nT (mult three4 b), add twoN nT)
                (addcomm4_at (mult three4 b, nT)) s2raw   (* le (n + mult3b)(2n + n) *)
    val s2b = le_cong_r4 (add nT (mult three4 b), add twoN nT, add nT twoN)
                (addcomm4_at (twoN, nT)) s2a   (* le (n + mult3b)(n + 2n) *)
    val sum_le = le_trans4_at (add (mult three4 a)(mult three4 b), add nT (mult three4 b), add nT twoN) s1 s2b
                 (* le (mult3a + mult3b)(n + 2n) *)
    (* left_distrib : mult 3 (a + b) = mult 3 a + mult 3 b.
       NB: left_distrib_v4's schematic vars are (k,m,n) NOT (x,m,n) — the base's
       left_distrib_4 instantiates "x" (a silent no-op).  Instantiate k/m/n here. *)
    val ld = beta_norm (Drule.infer_instantiate ctxtV4
               [(("k",0),ctermV4 three4),(("m",0),ctermV4 a),(("n",0),ctermV4 b)] left_distrib_v4)
             (* oeq (mult 3 (add a b))(add (mult 3 a)(mult 3 b)) *)
    (* rewrite sum_le's LEFT (mult3a+mult3b = qT) back to (mult 3 (a+b) = pT) : need oeq qT pT = sym ld *)
    val le3ab = le_cong_l4 (add (mult three4 a)(mult three4 b), mult three4 (add a b), add nT twoN) (oeq_sym OF [ld]) sum_le
                (* le (mult 3 (a+b))(n + 2n) *)
    (* n + 2n = 3n = mult 3 n : show oeq (add n (add n n))(mult 3 n) *)
    (* mult 3 n = n + n + n (mult_Suc twice).  mult 3 n = add n (mult 2 n) = add n (add n (mult 1 n)) = add n (add n n). *)
    val m3n_a = multSuc4_at (suc (suc ZeroC), nT)   (* oeq (mult 3 n)(add n (mult 2 n)) *)
    val m2n_a = multSuc4_at (suc ZeroC, nT)         (* oeq (mult 2 n)(add n (mult 1 n)) *)
    val m1n_a = mult1l4_at nT                       (* oeq (mult 1 n) n *)
    val m2n_b = oeq_trans OF [m2n_a, add_cong_r4 (nT, mult one4 nT, nT) m1n_a]  (* oeq (mult 2 n)(add n n) *)
    val m3n_b = oeq_trans OF [m3n_a, add_cong_r4 (nT, mult (suc (suc ZeroC)) nT, twoN) m2n_b]  (* oeq (mult 3 n)(add n (add n n)) *)
    (* so add n (2n) = mult 3 n via sym *)
    val le3ab_3n = le_cong_r4 (mult three4 (add a b), add nT twoN, mult three4 nT) (oeq_sym OF [m3n_b]) le3ab
                   (* le (mult 3 (a+b))(mult 3 n) *)
    val g = mult_le_cancel3 (add a b, nT) le3ab_3n   (* le (add a b) n *)
  in g end;

val () =
  (let val nF = Free("n_dsln",natT)
      val th = div_sum_le_n nF
  in out ("div_sum_le_n smoke : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of th) ^ "\n") end)
  handle e => out ("div_sum_le_n EXN : " ^ General.exnMessage e ^ "\n");
val () = out "W1_DIV_RDIV_OK\n";

(* ----------------------------------------------------------------------------
   (DIV)  div_reduce :  the multiply-back contradiction.
     Given (all on a Free n) :
        hThr : le (pow 4 n) (mult (Suc 2n)(mult (pow 2n (Suc s))(pow 4 (2n/3))))   [threshold RHS]
        hSEB : lt (mult (Suc 2n)(pow 2n (Suc s))) (pow 4 (rdiv n 3))               [the SEB]
     derive oFalse.
   Mechanics :
     Let Y = (Suc 2n)*(2n)^(Suc s),  Z = 4^(2n/3),  W = 4^(n/3).
     hSEB : le (Suc Y) W.
     mult_le_mono (right by Z) : le ((Suc Y)*Z)(W*Z).
     (Suc Y)*Z = Z + Y*Z  >= Suc(Y*Z)  since Z>=1  =>  le (Suc(Y*Z))((Suc Y)*Z).
        Hence le (Suc(Y*Z))(W*Z), i.e. lt (Y*Z)(W*Z).
     W*Z = 4^(n/3)*4^(2n/3) = 4^(n/3+2n/3) <= 4^n   [pow_add ; div_sum_le_n ; pow_le_exp].
        Hence lt (Y*Z)(4^n).
     hThr's RHS = (Suc 2n)*((2n)^(Suc s)*4^(2n/3)) = Y*Z  (assoc).  So le (4^n)(Y*Z).
     le (4^n)(Y*Z) and lt (Y*Z)(4^n) => lt (4^n)(4^n) => oFalse.
   ---------------------------------------------------------------------------- *)
fun div_reduce (sT, nT) hThr hSEB =
  let
    val twoN = add nT nT
    val Y = mult (suc twoN)(pow twoN (suc sT))         (* (2n+1)*(2n)^(s+1) *)
    val Z = pow fourC4 (rdiv twoN three4)              (* 4^(2n/3) *)
    val W = pow fourC4 (rdiv nT three4)                (* 4^(n/3) *)
    (* hSEB : le (Suc Y) W *)
    (* mult by Z on the right : mult_le_mono2_4_at (Suc Y, W, Z, Z) hSEB (le_refl Z) : le ((Suc Y)*Z)(W*Z) *)
    val mlm = mult_le_mono2_4_at (suc Y, W, Z, Z) hSEB (le_refl4_at Z)  (* le (mult (Suc Y) Z)(mult W Z) *)
    (* (Suc Y)*Z = add Z (mult Y Z)  [mult_Suc : mult (Suc Y) Z = add Z (mult Y Z)] *)
    val mSucYZ = multSuc4_at (Y, Z)   (* oeq (mult (Suc Y) Z)(add Z (mult Y Z)) *)
    (* le Z>=1 : pow_pos 4 (2n/3) : lt 0 Z = le 1 Z *)
    val zpos = pow_pos_4 (fourC4, rdiv twoN three4) lt0_4   (* le 1 Z *)
    (* Suc(Y*Z) = add 1 (Y*Z) <= add Z (Y*Z) [le_add_mono on 1<=Z] *)
    val addleft = le_add_mono_4 (one4, Z, mult Y Z) zpos   (* le (add 1 (Y*Z))(add Z (Y*Z)) *)
    (* add 1 (Y*Z) = Suc(Y*Z)  [add_Suc : add (Suc 0)(Y*Z) = Suc(add 0 (Y*Z)) ; add 0 = id] *)
    val a1 = add_Suc4_at (ZeroC, mult Y Z)   (* oeq (add (Suc 0)(Y*Z))(Suc(add 0 (Y*Z))) *)
    val a0 = add04_at (mult Y Z)             (* oeq (add 0 (Y*Z))(Y*Z) *)
    val sucEq = oeq_trans OF [a1, Suc_cong OF [a0]]   (* oeq (add 1 (Y*Z))(Suc(Y*Z)) *)
    (* le (Suc(Y*Z))(add Z (Y*Z)) *)
    val leSuc = le_cong_l4 (add one4 (mult Y Z), suc (mult Y Z), add Z (mult Y Z)) sucEq addleft
    (* le (Suc(Y*Z))(mult (Suc Y) Z) : rewrite add Z (Y*Z) back to (Suc Y)*Z *)
    val leSuc2 = le_cong_r4 (suc (mult Y Z), add Z (mult Y Z), mult (suc Y) Z) (oeq_sym OF [mSucYZ]) leSuc
                 (* le (Suc(Y*Z))(mult (Suc Y) Z) *)
    (* chain : le (Suc(Y*Z))((Suc Y)*Z) [leSuc2] ; le ((Suc Y)*Z)(W*Z) [mlm] -> le (Suc(Y*Z))(W*Z) = lt (Y*Z)(W*Z) *)
    val ltYZWZ = le_trans4_at (suc (mult Y Z), mult (suc Y) Z, mult W Z) leSuc2 mlm
                 (* le (Suc(Y*Z))(mult W Z) = lt (Y*Z)(W*Z) *)
    (* W*Z = 4^(n/3) * 4^(2n/3) = 4^(n/3 + 2n/3)  [pow_add sym] *)
    val padd = powadd4_at (fourC4, rdiv nT three4, rdiv twoN three4)
               (* oeq (pow 4 (add (n/3)(2n/3)))(mult (pow 4 (n/3))(pow 4 (2n/3))) = oeq (4^(n/3+2n/3))(W*Z) *)
    (* le (4^(n/3+2n/3))(4^n) : pow_le_exp (4>0, n/3+2n/3 <= n) *)
    val esum = div_sum_le_n nT   (* le (add (n/3)(2n/3)) n *)
    val pexp = pow_le_exp_4 (fourC4, add (rdiv nT three4)(rdiv twoN three4), nT) lt0_4 esum
               (* le (pow 4 (add (n/3)(2n/3)))(pow 4 n) *)
    (* rewrite : le (W*Z)(4^n) using padd (W*Z = 4^(n/3+2n/3)) on the left *)
    val leWZ4n = le_cong_l4 (pow fourC4 (add (rdiv nT three4)(rdiv twoN three4)), mult W Z, pow fourC4 nT) padd pexp
                 (* le (mult W Z)(pow 4 n) *)
    (* lt (Y*Z)(W*Z) and le (W*Z)(4^n) -> lt (Y*Z)(4^n) = le (Suc(Y*Z))(4^n) *)
    val ltYZ4n = le_trans4_at (suc (mult Y Z), mult W Z, pow fourC4 nT) ltYZWZ leWZ4n
                 (* le (Suc(Y*Z))(pow 4 n) = lt (Y*Z)(4^n) *)
    (* hThr : le (4^n)((Suc 2n)*((2n)^(Suc s)*Z)).  rewrite RHS to Y*Z by assoc :
       (Suc 2n)*((2n)^(Suc s)*Z) = ((Suc 2n)*(2n)^(Suc s))*Z = Y*Z  [mult_assoc sym]. *)
    val massoc = multassoc4_at (suc twoN, pow twoN (suc sT), Z)
                 (* oeq (mult (mult (Suc 2n)(pow 2n (Suc s))) Z)(mult (Suc 2n)(mult (pow 2n (Suc s)) Z)) *)
    (* so (Suc 2n)*((2n)^(Suc s)*Z) = Y*Z via sym massoc *)
    val hThrYZ = le_cong_r4 (pow fourC4 nT, mult (suc twoN)(mult (pow twoN (suc sT)) Z), mult Y Z)
                   (oeq_sym OF [massoc]) hThr
                 (* le (4^n)(Y*Z) *)
    (* le (4^n)(Y*Z) [hThrYZ] and lt (Y*Z)(4^n) [ltYZ4n] :
       lt (Y*Z)(4^n) = le (Suc(Y*Z))(4^n) ; le (4^n)(Y*Z) ; trans -> le (Suc(Y*Z))(Y*Z) = lt (Y*Z)(Y*Z) -> oFalse *)
    val ltSelf = le_trans4_at (suc (mult Y Z), pow fourC4 nT, mult Y Z) ltYZ4n hThrYZ
                 (* le (Suc(Y*Z))(Y*Z) = lt (Y*Z)(Y*Z) *)
    val g = lt_irrefl4_at (mult Y Z) OF [ltSelf]   (* oFalse *)
  in g end;

(* smoke test : feed assumptions, get oFalse *)
val () =
  let
    val sF = Free("s_dr",natT) val nF = Free("n_dr",natT)
    val twoN = add nF nF
    val Y = mult (suc twoN)(pow twoN (suc sF))
    val Z = pow fourC4 (rdiv twoN three4)
    val W = pow fourC4 (rdiv nF three4)
    val hThr = Thm.assume (ctermV4 (jT (le (pow fourC4 nF)(mult (suc twoN)(mult (pow twoN (suc sF)) Z)))))
    val hSEB = Thm.assume (ctermV4 (jT (lt Y W)))   (* lt Y W = le (Suc Y) W *)
    val th = div_reduce (sF, nF) hThr hSEB
    val isFalse = (Thm.prop_of th) aconv (jT oFalseC)
  in out ("div_reduce smoke : concl is oFalse = " ^ Bool.toString isFalse ^ "\n") end;

val () = out "W1_DIV_REDUCE_OK\n";

(* SUFFICES marker : div_reduce closes (the reduction is valid).  We GATE it on a
   fresh smoke proof producing oFalse from the two assumptions, 0-hyp modulo the
   two discharged assumptions (it carries exactly hThr+hSEB as hyps, by design). *)
val suffices_ok =
  let
    val sF = Free("s_suf",natT) val nF = Free("n_suf",natT)
    val twoN = add nF nF
    val Y = mult (suc twoN)(pow twoN (suc sF))
    val Z = pow fourC4 (rdiv twoN three4)
    val W = pow fourC4 (rdiv nF three4)
    val hThrP = jT (le (pow fourC4 nF)(mult (suc twoN)(mult (pow twoN (suc sF)) Z)))
    val hSEBP = jT (lt Y W)
    val hThr = Thm.assume (ctermV4 hThrP)
    val hSEB = Thm.assume (ctermV4 hSEBP)
    val th = div_reduce (sF, nF) hThr hSEB
    (* discharge both : meta-impl hThr ==> hSEB ==> oFalse, 0-hyp *)
    val d = Thm.implies_intr (ctermV4 hThrP) (Thm.implies_intr (ctermV4 hSEBP) th)
    val dd = Thm.implies_intr (ctermV4 hSEBP) (Thm.implies_intr (ctermV4 hThrP) th)
    val concl_false = (Thm.prop_of th) aconv (jT oFalseC)
    val zero_hyp = zhV4 d
  in concl_false andalso zero_hyp end;
val () = if suffices_ok then out "SUFFICES_OK\n" else out "SUFFICES_FAIL\n";
val () = out "W1_SUFFICES_DONE\n";

(* ============================================================================
   (SEB)  the sub-exponential bound  4^(n/3) > (2n+1)*(2n)^(s+1)  for n >= N0.
   ----------------------------------------------------------------------------
   STEP 1 (the SEB REDUCTION, fully symbolic, banked 0-hyp + aconv) :
     from the floor_sqrt facts  s*s <= 2n  and  2n < (Suc s)^2  derive
        (2n+1)*(2n)^(Suc s)  <=  ((Suc s)^2)^(Suc(Suc s))      [= (s+1)^(2s+4)]
     i.e. seb_reduce :
        jT (lt (add n n)(mult (Suc s)(Suc s)))                 (* 2n < (s+1)^2 *)
          ==> le (mult (Suc 2n)(pow 2n (Suc s)))
                 (pow (mult (Suc s)(Suc s)) (Suc(Suc s)))
     PROOF :  K := (Suc s)^2 = mult (Suc s)(Suc s).
        2n+1 = Suc 2n <= K            [hSsq : 2n < K]
        2n   <= Suc 2n <= K           [le_suc_self + trans]
        (2n)^(Suc s) <= K^(Suc s)     [pow_le_mono_base]
        (2n+1)*(2n)^(Suc s) <= K * K^(Suc s)   [mult_le_mono2]
        K * K^(Suc s) = K^(Suc(Suc s)) [pow_Suc, sym]
   ============================================================================ *)
val () = out "W1_SEB_BEGIN\n";

fun seb_reduce (sT, nT) hSsq =   (* hSsq : jT (lt (add n n)(mult (Suc s)(Suc s))) *)
  let
    val twoN = add nT nT
    val K    = mult (suc sT)(suc sT)        (* (Suc s)^2 *)
    (* hSsq : lt 2n K = le (Suc 2n) K *)
    val le_S2n_K = hSsq                       (* le (Suc 2n) K *)
    (* le 2n (Suc 2n) ; trans -> le 2n K *)
    val le_2n_K  = le_trans4_at (twoN, suc twoN, K) (le_suc_self4_at twoN) le_S2n_K   (* le 2n K *)
    (* (2n)^(Suc s) <= K^(Suc s) *)
    val powmono = pow_le_mono_base_4 (twoN, K, suc sT) le_2n_K   (* le (pow 2n (Suc s))(pow K (Suc s)) *)
    (* (2n+1)*(2n)^(Suc s) <= K * K^(Suc s)  [mult_le_mono2 : le (Suc 2n) K , le (pow 2n (Suc s))(pow K (Suc s))] *)
    val mlm = mult_le_mono2_4_at (suc twoN, K, pow twoN (suc sT), pow K (suc sT)) le_S2n_K powmono
              (* le (mult (Suc 2n)(pow 2n (Suc s)))(mult K (pow K (Suc s))) *)
    (* K * K^(Suc s) = K^(Suc(Suc s))  [pow_Suc : pow K (Suc(Suc s)) = mult K (pow K (Suc s))] *)
    val pSucK = powSuc4_at (K, suc sT)   (* oeq (pow K (Suc(Suc s)))(mult K (pow K (Suc s))) *)
    (* rewrite RHS of mlm : mult K (pow K (Suc s)) -> pow K (Suc(Suc s)) via sym pSucK *)
    val g = le_cong_r4 (mult (suc twoN)(pow twoN (suc sT)), mult K (pow K (suc sT)), pow K (suc (suc sT)))
              (oeq_sym OF [pSucK]) mlm
            (* le (mult (Suc 2n)(pow 2n (Suc s)))(pow K (Suc(Suc s))) *)
  in g end;

(* bank : discharge hSsq, then VARIFY to schematic, aconv against the interface. *)
val seb_reduce_thm =
  let
    val sF = Free("s_sr2",natT) val nF = Free("n_sr2",natT)
    val twoN = add nF nF
    val K = mult (suc sF)(suc sF)
    val hSsqP = jT (lt twoN K)
    val hSsq = Thm.assume (ctermV4 hSsqP)
    val th = seb_reduce (sF, nF) hSsq
    val d = Thm.implies_intr (ctermV4 hSsqP) th
  in varify d end;

val () = out ("seb_reduce_thm 0hyp=" ^ Bool.toString (zhV4 seb_reduce_thm) ^ "\n");
val () = out ("seb_reduce_thm : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of seb_reduce_thm) ^ "\n");

val i_seb_reduce =
  let val sVz = Var(("s_sr2",0),natT) val nVz = Var(("n_sr2",0),natT)
      val twoN = add nVz nVz val K = mult (suc sVz)(suc sVz)
  in Logic.mk_implies (jT (lt twoN K),
       jT (le (mult (suc twoN)(pow twoN (suc sVz)))
              (pow K (suc (suc sVz))))) end;
val r_sr = (Thm.prop_of seb_reduce_thm) aconv i_seb_reduce;
val () = out ("seb_reduce_thm aconv=" ^ Bool.toString r_sr ^ "\n");
val seb_reduce_closed = zhV4 seb_reduce_thm andalso r_sr;
val () = if seb_reduce_closed then out "SEB_REDUCE_OK\n" else out "SEB_REDUCE_FAIL\n";
val () = out "W1_SEB_REDUCE_DONE\n";

(* ----------------------------------------------------------------------------
   guard_le_third :  le (mult s s)(add n n) ==> le 3 s ==> le s (rdiv (add n n) 3)
     i.e. s = floor_sqrt(2n) with s >= 3 satisfies the threshold guard s <= 2n/3.
   PROOF : 3*s <= s*s <= 2n  [le 3 s -> mult_le_mono ; trans].  Suppose lt (2n/3) s,
     i.e. le (Suc(2n/3)) s.  Then 3*(Suc(2n/3)) <= 3*s, but 2n < 3*(Suc(2n/3)) and
     3*s <= 2n, so 3*s <= 2n < 3*(Suc(2n/3)) <= 3*s : lt (3*s)(3*s), oFalse.
     nlt_le : neg(lt (2n/3) s) -> le s (2n/3).
   ---------------------------------------------------------------------------- *)
fun guard_le_third (sT, nT) hSq hs3 =   (* hSq : le (s*s)(2n) ; hs3 : le 3 s *)
  let
    val twoN = add nT nT
    val q3   = rdiv twoN three4
    (* 3*s <= s*s : mult_le_mono (s, 3, s) hs3 : le (mult s 3)(mult s s) ; commute mult s 3 = 3 s *)
    val ms3  = mult_le_mono_4 (sT, three4, sT) hs3   (* le (mult s 3)(mult s s) *)
    val cmS3 = multcomm4_at (sT, three4)             (* oeq (mult s 3)(mult 3 s) *)
    val le3s_ss = le_cong_l4 (mult sT three4, mult three4 sT, mult sT sT) cmS3 ms3   (* le (mult 3 s)(mult s s) *)
    val le3s_2n = le_trans4_at (mult three4 sT, mult sT sT, twoN) le3s_ss hSq   (* le (mult 3 s)(2n) *)
    (* prove neg (lt q3 s) *)
    val hAssume = Thm.assume (ctermV4 (jT (lt q3 sT)))   (* le (Suc q3) s *)
    val le3Sq3_3s = mult_le_mono_4 (three4, suc q3, sT) hAssume   (* le (mult 3 (Suc q3))(mult 3 s) *)
    val lt2n3Sq3  = two_n_lt_3_succ_div nT   (* le (Suc 2n)(mult 3 (Suc q3)) = lt 2n (mult 3 (Suc q3)) *)
    (* 3s <= 2n = lt2n... : le (mult 3 s)(2n) ; lt 2n (mult 3 (Suc q3)) = le (Suc 2n)(...) ;
       chain to le (Suc(mult 3 s))(mult 3 (Suc q3)) then <= mult 3 s -> lt (mult 3 s)(mult 3 s). *)
    (* le (Suc(mult 3 s))(Suc 2n) [le_suc_mono of le3s_2n] *)
    val leS3s_S2n = le_suc_mono4_at (mult three4 sT, twoN) le3s_2n   (* le (Suc(3s))(Suc 2n) *)
    val leS3s_3Sq3 = le_trans4_at (suc (mult three4 sT), suc twoN, mult three4 (suc q3)) leS3s_S2n lt2n3Sq3
                     (* le (Suc(3s))(mult 3 (Suc q3)) *)
    val ltSelf = le_trans4_at (suc (mult three4 sT), mult three4 (suc q3), mult three4 sT) leS3s_3Sq3 le3Sq3_3s
                 (* le (Suc(3s))(3s) = lt (3s)(3s) *)
    val ff = lt_irrefl4_at (mult three4 sT) OF [ltSelf]   (* oFalse *)
    val hngMeta = Thm.implies_intr (ctermV4 (jT (lt q3 sT))) ff   (* meta : (lt q3 s) ==> oFalse *)
    val hng = impI_4 (lt q3 sT, oFalseC) hngMeta   (* object neg (lt q3 s) = Imp (lt q3 s) oFalse *)
    val g = nlt_le_4 (q3, sT) hng   (* le s q3 *)
  in g end;

val () =
  (let val sF = Free("s_gd",natT) val nF = Free("n_gd",natT)
       val hSq = Thm.assume (ctermV4 (jT (le (mult sF sF)(add nF nF))))
       val hs3 = Thm.assume (ctermV4 (jT (le three4 sF)))
       val th = guard_le_third (sF, nF) hSq hs3
   in out ("guard_le_third smoke : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of th) ^ "\n") end)
  handle e => out ("guard_le_third EXN : " ^ General.exnMessage e ^ "\n");
val () = out "W1_GUARD_DONE\n";

(* ----------------------------------------------------------------------------
   s_ge_3 :  le 9 (add n n) ==> lt (add n n)(mult (Suc s)(Suc s)) ==> le 3 s
     (the floor witness for 2n >= 9 has s >= 3).
   PROOF : suppose lt s 3 (= le (Suc s) 3).  Then (Suc s) <= 3, so (Suc s)^2 <= 9
     [mult_le_mono2].  But 9 <= 2n < (Suc s)^2 <= 9 : lt 9 9, oFalse.  nlt_le.
   ---------------------------------------------------------------------------- *)
val nine4 = mkNum 9;
fun s_ge_3 (sT, nT) h9 hSsq =   (* h9 : le 9 (2n) ; hSsq : lt 2n ((Suc s)^2) ; result : le 3 s *)
  let
    val twoN = add nT nT
    (* prove neg (lt s 3), then nlt_le (3,s) gives le 3 s *)
    val hAssume = Thm.assume (ctermV4 (jT (lt sT three4)))   (* lt s 3 = le (Suc s) 3 *)
    (* (Suc s)^2 <= 3*3 : mult_le_mono2 (le (Suc s) 3)(le (Suc s) 3) *)
    val leSq33 = mult_le_mono2_4_at (suc sT, three4, suc sT, three4) hAssume hAssume
                 (* le (mult (Suc s)(Suc s))(mult 3 3) *)
    (* mult 3 3 = 9 via mult_eval *)
    val (nineT, m33eq) = mult_eval three4 three4   (* (mkNum 9, oeq (mult 3 3)(mkNum 9)) *)
    val leSq9 = le_cong_r4 (mult (suc sT)(suc sT), mult three4 three4, nineT) m33eq leSq33
                (* le ((Suc s)^2) 9 *)
    (* lt 2n ((Suc s)^2) [hSsq] ; le ((Suc s)^2) 9 -> lt 2n 9 = le (Suc 2n) 9 *)
    val lt2n9 = le_trans4_at (suc twoN, mult (suc sT)(suc sT), nineT) hSsq leSq9   (* le (Suc 2n) 9 *)
    (* le 9 2n [h9] ; le (Suc 2n) 9 -> le (Suc 2n) 2n = lt 2n 2n -> oFalse *)
    val ltSelf = le_trans4_at (suc twoN, nineT, twoN) lt2n9 h9   (* le (Suc 2n)(2n) = lt 2n 2n *)
    val ff = lt_irrefl4_at twoN OF [ltSelf]   (* oFalse *)
    val hngMeta = Thm.implies_intr (ctermV4 (jT (lt sT three4))) ff   (* meta (lt s 3) ==> oFalse *)
    val hng = impI_4 (lt sT three4, oFalseC) hngMeta   (* object neg (lt s 3) *)
    val g = nlt_le_4 (sT, three4) hng   (* nlt_le (d=s,c=3): neg(lt s 3) -> le 3 s *)
  in g end;

val () =
  (let val sF = Free("s_sge",natT) val nF = Free("n_sge",natT)
       val h9  = Thm.assume (ctermV4 (jT (le nine4 (add nF nF))))
       val hSsq= Thm.assume (ctermV4 (jT (lt (add nF nF)(mult (suc sF)(suc sF)))))
       val th = s_ge_3 (sF, nF) h9 hSsq
   in out ("s_ge_3 smoke : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of th) ^ "\n") end)
  handle e => out ("s_ge_3 EXN : " ^ General.exnMessage e ^ "\n");
val () = out "W1_SGE3_DONE\n";

(* ============================================================================
   (TH)  threshold contradiction — CONDITIONAL ON SEB.
   ----------------------------------------------------------------------------
   The SEB itself (4^(n/3) > (2n+1)(2n)^(s+1)) is the analytic wall whose base
   case at n~516 is a ~100-digit number — INFEASIBLE as a unary Suc-tower (the
   intrinsic limit documented in the base file).  We therefore prove the
   threshold contradiction MODULO SEB : taking SEB as a meta-universal hypothesis
       SEB_HYP n :=  !!s. (le (mult s s)(2n)) ==> (lt (2n)(mult (Suc s)(Suc s)))
                         ==> jT (lt (mult (Suc 2n)(pow 2n (Suc s)))(pow 4 (rdiv n 3)))
   we derive, fully in the kernel,
       th_given_seb : SEB_HYP n ==> H n ==> lt 0 n ==> lt 0 (binom 2n n)
                       ==> le 9 (2n) ==> oFalse.
   This shows the ENTIRE remaining Erdos structure is closed : SEB is the SOLE
   missing input, and supplying it (the numeric wall) closes Bertrand.
   ============================================================================ *)
val () = out "W1_TH_BEGIN\n";

(* SEB meta-hyp proposition builder for a given n (Free or otherwise). *)
fun seb_hyp_prop nT =
  let
    val twoN = add nT nT
    val sB = Free("s_seb", natT)
    val body = Logic.mk_implies (jT (le (mult sB sB) twoN),
                 Logic.mk_implies (jT (lt twoN (mult (suc sB)(suc sB))),
                   jT (lt (mult (suc twoN)(pow twoN (suc sB)))(pow fourC4 (rdiv nT three4)))))
  in Logic.all sB body end;

fun th_given_seb_body nT =
  let
    val twoN = add nT nT
    val R    = binom twoN nT
    val q3   = rdiv twoN three4
    (* hypotheses *)
    val hSEB = Thm.assume (ctermV4 (seb_hyp_prop nT))     (* the meta-universal SEB *)
    val hH   = Thm.assume (ctermV4 (H_prop nT))           (* H : no prime in (n,2n] *)
    val hn0  = Thm.assume (ctermV4 (jT (lt ZeroC nT)))    (* lt 0 n *)
    val hR0  = Thm.assume (ctermV4 (jT (lt ZeroC R)))     (* lt 0 (binom 2n n) *)
    val h9   = Thm.assume (ctermV4 (jT (le nine4 twoN)))  (* le 9 (2n) *)
    (* threshold_assembled OF [hn0, hR0, hH] : jT (Ex s. (sq facts) /\ (guard -> 4^n <= ...)) *)
    val thA = ((threshold_assembled OF [hn0]) OF [hR0]) OF [hH]
    (* outBody matching threshold_assembled's existential *)
    fun outBody sT = mkConj (mkConj (le (mult sT sT) twoN)(lt twoN (mult (suc sT)(suc sT))))
                            (mkImp (le sT q3)
                              (le (pow fourC4 nT)
                                  (mult (suc twoN)(mult (pow twoN (suc sT))(pow fourC4 q3)))))
    val outAbs = Term.lambda (Free("s_out", natT)) (outBody (Free("s_out", natT)))
    val goalC = oFalseC
    fun body sF (hs : thm) =   (* hs : outBody sF *)
      let
        val sq  = mult sF sF
        val sqS = mult (suc sF)(suc sF)
        (* split *)
        val hSqFacts = conjunct1_4 (mkConj (le sq twoN)(lt twoN sqS),
                                    mkImp (le sF q3)(le (pow fourC4 nT)(mult (suc twoN)(mult (pow twoN (suc sF))(pow fourC4 q3))))) hs
        val hCond    = conjunct2_4 (mkConj (le sq twoN)(lt twoN sqS),
                                    mkImp (le sF q3)(le (pow fourC4 nT)(mult (suc twoN)(mult (pow twoN (suc sF))(pow fourC4 q3))))) hs
        val hSq      = conjunct1_4 (le sq twoN, lt twoN sqS) hSqFacts   (* le (s*s)(2n) *)
        val hSsq     = conjunct2_4 (le sq twoN, lt twoN sqS) hSqFacts   (* lt 2n ((Suc s)^2) *)
        (* le 3 s [s_ge_3] ; le s q3 [guard_le_third] *)
        val hs3      = s_ge_3 (sF, nT) h9 hSsq                  (* le 3 s *)
        val hGuard   = guard_le_third (sF, nT) hSq hs3          (* le s q3 *)
        (* discharge guard -> threshold bound *)
        val hThr     = mp_4 (le sF q3, le (pow fourC4 nT)(mult (suc twoN)(mult (pow twoN (suc sF))(pow fourC4 q3)))) hCond hGuard
                       (* le (4^n)((2n+1)*((2n)^(Suc s)*4^(2n/3))) *)
        (* SEB at this s : forall_elim sF on hSEB, then discharge floor facts *)
        val sebAt    = Thm.forall_elim (ctermV4 sF) hSEB
                       (* (le (s*s)(2n)) ==> (lt 2n ((Suc s)^2)) ==> jT (lt ((2n+1)(2n)^(Suc s))(4^(n/3))) *)
        val hSEBineq = (sebAt OF [hSq]) OF [hSsq]   (* lt ((2n+1)(2n)^(Suc s))(4^(n/3)) *)
        (* div_reduce : hThr + hSEBineq -> oFalse *)
        val ff = div_reduce (sF, nT) hThr hSEBineq
      in ff end
    val concl = exE_elim4 (outAbs, goalC) thA "s_th_seb" body
    (* discharge the five hypotheses in a fixed order *)
    val d5 = Thm.implies_intr (ctermV4 (jT (le nine4 twoN))) concl
    val d4 = Thm.implies_intr (ctermV4 (jT (lt ZeroC R))) d5
    val d3 = Thm.implies_intr (ctermV4 (jT (lt ZeroC nT))) d4
    val d2 = Thm.implies_intr (ctermV4 (H_prop nT)) d3
    val d1 = Thm.implies_intr (ctermV4 (seb_hyp_prop nT)) d2
  in d1 end;

val th_given_seb = varify (th_given_seb_body (Free("n_th_gs", natT)));

val () = out ("th_given_seb 0hyp=" ^ Bool.toString (zhV4 th_given_seb) ^ "\n");
val () = out ("th_given_seb : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of th_given_seb) ^ "\n");

(* aconv check : SEB_HYP ==> H ==> lt 0 n ==> lt 0 binom ==> le 9 2n ==> oFalse *)
val i_th_given_seb =
  let val nVz = Var(("n_th_gs",0),natT)
      val twoN = add nVz nVz val R = binom twoN nVz
      (* SEB_HYP with bound s (Logic.all over Free s_seb) *)
      val sB = Free("s_seb", natT)
      val sebBody = Logic.mk_implies (jT (le (mult sB sB) twoN),
                      Logic.mk_implies (jT (lt twoN (mult (suc sB)(suc sB))),
                        jT (lt (mult (suc twoN)(pow twoN (suc sB)))(pow fourC4 (rdiv nVz three4)))))
      val sebHyp = Logic.all sB sebBody
  in Logic.mk_implies (sebHyp,
       Logic.mk_implies (H_prop nVz,
         Logic.mk_implies (jT (lt ZeroC nVz),
           Logic.mk_implies (jT (lt ZeroC R),
             Logic.mk_implies (jT (le nine4 twoN), jT oFalseC))))) end;
val r_tgs = (Thm.prop_of th_given_seb) aconv i_th_given_seb;
val () = out ("th_given_seb aconv=" ^ Bool.toString r_tgs ^ "\n");
val threshold_given_seb_ok = zhV4 th_given_seb andalso r_tgs;
val () = if threshold_given_seb_ok then out "THRESHOLD_GIVEN_SEB_OK\n" else out "THRESHOLD_GIVEN_SEB_FAIL\n";
val () = out "W1_TH_DONE\n";

(* ============================================================================
   (BL)  bertrand_large — CONDITIONAL ON SEB.
   ----------------------------------------------------------------------------
   bertrand_large_given_seb :
       SEB_HYP n ==> le N0 n ==> Ex p. prime2 p /\ lt n p /\ le p (add n n)
   with N0 = 513 (<= 631, so the banked small-n chain — reachable via prime2 up
   to 631 — covers n < N0).  By contradiction : assume H, derive oFalse via
   th_given_seb, then double-negation-eliminate to the prime-existence statement.
   The n>=N0 hyps lt 0 n / le 9 2n / lt 0 (binom 2n n) are derived from le N0 n.
   ============================================================================ *)
val () = out "W1_BL_BEGIN\n";

val N0num = mkNum 513;   (* the explicit threshold ; 513 <= 631 *)

val binom_pos_v4 = varify binom_pos;
fun binom_pos_4 (nT,kT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtV4
        [(("n",0), ctermV4 nT),(("k",0), ctermV4 kT)] binom_pos_v4)) h;
val dbl_neg_v4 = varify dbl_neg;
fun dbl_neg_4 At h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtV4
        [(("A",0), ctermV4 At)] dbl_neg_v4)) h;

fun bertrand_large_given_seb_body nT =
  let
    val twoN = add nT nT
    val R    = binom twoN nT
    (* hypotheses *)
    val hSEB  = Thm.assume (ctermV4 (seb_hyp_prop nT))   (* SEB meta-universal *)
    val hN0   = Thm.assume (ctermV4 (jT (le N0num nT)))  (* le 513 n *)
    (* derive : le n (2n), lt 0 n, le 9 (2n), lt 0 (binom 2n n) *)
    val le_n_2n = le_add4_at (nT, nT)                    (* le n (2n) *)
    val le1N0   = le_eval 1 513                          (* le 1 513 *)
    val lt0n    = le_trans4_at (one4, N0num, nT) le1N0 hN0   (* le 1 n = lt 0 n *)
    val le9N0   = le_eval 9 513                          (* le 9 513 *)
    val le9n    = le_trans4_at (nine4, N0num, nT) le9N0 hN0  (* le 9 n *)
    val le9_2n  = le_trans4_at (nine4, nT, twoN) le9n le_n_2n  (* le 9 (2n) *)
    val ltR0    = binom_pos_4 (twoN, nT) le_n_2n         (* lt 0 (binom 2n n) *)
    (* assume H, derive oFalse via th_given_seb *)
    val hH      = Thm.assume (ctermV4 (H_prop nT))       (* neg (Ex p. H_body) *)
    (* th_given_seb is varified ; re-instantiate at nT.  Its shape :
         SEB_HYP ?n ==> H ?n ==> lt 0 ?n ==> lt 0 (binom 2?n ?n) ==> le 9 (2?n) ==> oFalse *)
    val thAtN = beta_norm (Drule.infer_instantiate ctxtV4 [(("n_th_gs",0), ctermV4 nT)] th_given_seb)
    (* use implies_elim (direct modus ponens) — OF's resolution chokes on the
       higher-order meta-\<And>s_seb SEB premise; the premises match exactly. *)
    val ffMeta = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
                   (Thm.implies_elim (Thm.implies_elim thAtN hSEB) hH) lt0n) ltR0) le9_2n  (* oFalse *)
    (* neg H = neg (neg (Ex p. H_body)) : implies_intr H over oFalse, then to object neg *)
    val negH_meta = Thm.implies_intr (ctermV4 (H_prop nT)) ffMeta   (* meta : H ==> oFalse *)
    val ExBody = mkEx (H_abs nT)   (* Ex p. prime2 p /\ (lt n p /\ le p 2n) *)
    (* H_prop nT = jT (neg ExBody) ; so negH_meta : jT (neg ExBody) ==> jT oFalse, i.e. meta-neg of (neg ExBody).
       Convert to object neg (neg ExBody) via impI_4, then dbl_neg. *)
    val negH_obj = impI_4 (neg ExBody, oFalseC) negH_meta   (* object neg (neg ExBody) *)
    val gEx = dbl_neg_4 ExBody negH_obj   (* jT ExBody *)
    (* discharge the two outer hyps : SEB_HYP, le N0 n *)
    val d2 = Thm.implies_intr (ctermV4 (jT (le N0num nT))) gEx
    val d1 = Thm.implies_intr (ctermV4 (seb_hyp_prop nT)) d2
  in d1 end;

val bertrand_large_given_seb = varify (bertrand_large_given_seb_body (Free("n_bl", natT)));

val () = out ("bertrand_large_given_seb 0hyp=" ^ Bool.toString (zhV4 bertrand_large_given_seb) ^ "\n");
val () = out ("bertrand_large_given_seb hyps=" ^ Int.toString (length (Thm.hyps_of bertrand_large_given_seb))
              ^ " extra_shyps=" ^ Int.toString (length (Thm.extra_shyps bertrand_large_given_seb)) ^ "\n");
val () = out ("bertrand_large_given_seb : " ^ Syntax.string_of_term ctxtV4 (Thm.prop_of bertrand_large_given_seb) ^ "\n");

(* aconv : SEB_HYP ==> le 513 n ==> Ex p. prime2 p /\ (lt n p /\ le p 2n) *)
val i_bl_given_seb =
  let val nVz = Var(("n_bl",0),natT)
      val twoN = add nVz nVz
      val sB = Free("s_seb", natT)
      val sebBody = Logic.mk_implies (jT (le (mult sB sB) twoN),
                      Logic.mk_implies (jT (lt twoN (mult (suc sB)(suc sB))),
                        jT (lt (mult (suc twoN)(pow twoN (suc sB)))(pow fourC4 (rdiv nVz three4)))))
      val sebHyp = Logic.all sB sebBody
      val bb = Term.lambda (Free("p_H", natT))
                 (mkConj (prime2 (Free("p_H", natT)))
                         (mkConj (lt nVz (Free("p_H", natT)))(le (Free("p_H", natT)) twoN)))
  in Logic.mk_implies (sebHyp,
       Logic.mk_implies (jT (le N0num nVz), jT (mkEx bb))) end;
val r_bl = (Thm.prop_of bertrand_large_given_seb) aconv i_bl_given_seb;
val () = out ("bertrand_large_given_seb aconv=" ^ Bool.toString r_bl ^ "\n");
val bl_given_seb_ok = zhV4 bertrand_large_given_seb andalso r_bl;
val () = if bl_given_seb_ok then out "BERTRAND_LARGE_GIVEN_SEB_OK\n" else out "BERTRAND_LARGE_GIVEN_SEB_FAIL\n";

(* soundness probe : replacing le p 2n by le p n (no prime in (n,n]) must NOT be aconv *)
val s_bl_range =
  let val nVz = Var(("n_bl",0),natT) val twoN = add nVz nVz
      val sB = Free("s_seb", natT)
      val sebBody = Logic.mk_implies (jT (le (mult sB sB) twoN),
                      Logic.mk_implies (jT (lt twoN (mult (suc sB)(suc sB))),
                        jT (lt (mult (suc twoN)(pow twoN (suc sB)))(pow fourC4 (rdiv nVz three4)))))
      val sebHyp = Logic.all sB sebBody
      val bb = Term.lambda (Free("p_H", natT))
                 (mkConj (prime2 (Free("p_H", natT)))
                         (mkConj (lt nVz (Free("p_H", natT)))(le (Free("p_H", natT)) nVz)))  (* le p n — wrong *)
      val bad = Logic.mk_implies (sebHyp, Logic.mk_implies (jT (le N0num nVz), jT (mkEx bb)))
  in not ((Thm.prop_of bertrand_large_given_seb) aconv bad) end;
val () = out ("PROBE bl-range-is-2n=" ^ Bool.toString s_bl_range ^ "\n");
val () = out "W1_BL_DONE\n";

(* ============================================================================
   W1 FINALE — honest audit + the precise blocker.
   ----------------------------------------------------------------------------
   PROVED this appendix (all 0-hyp + aconv on ctxtV4, the kernel checking every
   inference under Proofterm.proofs:=0) :
     div_reduce / suffices_ok        — the divide/multiply-back reduction.   [SUFFICES_OK]
     seb_reduce_thm                  — (2n+1)(2n)^(s+1) <= ((s+1)^2)^(s+2).  [SEB_REDUCE_OK]
     guard_le_third                  — s*s<=2n /\ s>=3 ==> s <= 2n/3 (the threshold guard).
     s_ge_3                          — 2n>=9 /\ 2n<(s+1)^2 ==> s >= 3.
     th_given_seb                    — SEB_HYP n ==> H ==> ... ==> oFalse.   [THRESHOLD_GIVEN_SEB_OK]
     bertrand_large_given_seb        — SEB_HYP n ==> le 513 n ==> Ex prime in (n,2n].
                                                                              [BERTRAND_LARGE_GIVEN_SEB_OK]
   NOT closed (the analytic wall) :
     SEB itself : 4^(n/3) > (2n+1)(2n)^(s+1) for n >= N0 (N0 = 513 <= 631).
     It is exp-vs-sub-exp ; reduce_seb leaves the power-vs-power comparison
        ((s+1)^2)^(s+2) < 4^(n/3),
     whose smallest valid threshold (n ~ 516) forces a CONCRETE base case ~ 4^172,
     a ~100-DECIMAL-DIGIT number — INFEASIBLE as a unary Suc-tower nat (the base
     file already documents this exact cap : "the unary-numeral term blowup").
     Both the bitlen/log route and the strong-induction route bottom out in the
     SAME concrete crossover numeral, so the blocker is INTRINSIC to the unary
     encoding, not to the proof strategy.
   The explicit N0 is 513 (<= 631), so the banked small-n chain (prime2 up to 631)
   covers n < N0 ; supplying SEB closes the full Bertrand's postulate.
   ============================================================================ *)
val () = out "W1_FINALE_BEGIN\n";

(* axiom audit : a NEW const must NOT have been added (we added none) ; the only
   classical axiom is ex_middle ; no smuggled threshold/bertrand/prime-existence axiom. *)
val () =
  let
    val thy = Proof_Context.theory_of ctxtV4
    val axs = Theory.all_axioms_of thy
    val names = map fst axs
    val hasEM = List.exists (fn s => String.isSubstring "ex_middle" s
                                     orelse String.isSubstring "excluded" s) names
    val nClassical = length (List.filter (fn s => String.isSubstring "ex_middle" s
                                     orelse String.isSubstring "excluded" s) names)
    val suspicious = List.filter (fn s =>
         String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s
         orelse String.isSubstring "chebyshev" s orelse String.isSubstring "postulate" s
         orelse String.isSubstring "seb" s orelse String.isSubstring "threshold" s
         orelse String.isSubstring "bitlen" s) names
  in out ("W1_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " ex_middle_present=" ^ Bool.toString hasEM
          ^ " classical_count=" ^ Int.toString nClassical
          ^ " suspicious_count=" ^ Int.toString (length suspicious) ^ "\n");
     app (fn s => out ("  W1 SUSPICIOUS AXIOM: " ^ s ^ "\n")) suspicious
  end;

(* honest SEB status *)
val seb_closed = false;   (* the numeric crossover base case is infeasible in unary *)
val () = if seb_closed then out "SEB_OK\n" else out "SEB_BLOCKED_UNARY_NUMERAL_WALL\n";
(* TH and BL are closed CONDITIONALLY on SEB (the unconditional forms need SEB) *)
val () = out ("THRESHOLD_OK status : conditional (THRESHOLD_GIVEN_SEB_OK=" ^ Bool.toString threshold_given_seb_ok ^ ")\n");
val () = out ("BERTRAND_LARGE_OK status : conditional (BERTRAND_LARGE_GIVEN_SEB_OK=" ^ Bool.toString bl_given_seb_ok ^ ")\n");

val w1_structural_all =
  suffices_ok andalso seb_reduce_closed andalso threshold_given_seb_ok andalso bl_given_seb_ok andalso s_bl_range;
val () = if w1_structural_all then out "BERTRAND_W1_STRUCTURE_OK\n" else out "BERTRAND_W1_STRUCTURE_FAIL\n";
(* the FULL unconditional bertrand_large is NOT closed (SEB wall) *)
val () = if seb_closed andalso w1_structural_all then out "BERTRAND_W1_ALL_OK\n"
         else out "BERTRAND_W1_PARTIAL (SEB analytic wall : unary-numeral crossover base case)\n";
val () = out "W1_FINALE_DONE\n";
val () = OS.Process.exit OS.Process.success;
