(* ============================================================================
   CLOSED-FORM SUMMATION THEOREMS in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_summation_forms.rs)
   ----------------------------------------------------------------------------
   Three named closed-form sums, each a 0-hypothesis theorem by genuine LCF
   kernel inference over the higher-order finite sum sumf (no new constant,
   pure identities; numerals are Suc-chains, sums cleared of denominators to
   stay in the naturals):

     nicomachus   : |- sumf (%k. k*k*k) n = (sumf (%k. k) n) * (sumf (%k. k) n)
                    0^3 + 1^3 + ... + n^3 = (0+1+...+n)^2  (Nicomachus's theorem),
                    via the Gauss-doubling helper gauss2 (2*sum = n*(n+1)).
     faulhaber_sq : |- 6 * sumf (%k. k*k) n = n*(n+1)*(2n+1)
                    6*(0^2+...+n^2) = n(n+1)(2n+1)  (Faulhaber, sum of squares).
     pronic_sum   : |- 3 * sumf (%k. k*(k+1)) n = n*(n+1)*(n+2)
                    3*(0*1 + 1*2 + ... + n*(n+1)) = n(n+1)(n+2).

   Each is proved by nat induction with the semiring algebra (left/right_distrib,
   mult/add comm/assoc) and carries a soundness probe. Built on the finite-sum
   development (isabelle_binom_thm.sml) over the classical foundation, spliced in
   by common::with_binom_thm. Proved by a multi-seat ultracode fleet racing all
   three concurrently (wf_62507100-db8); re-verified end-to-end by hand.
   ============================================================================ *)

(* ============================================================================
   ***  NICOMACHUS'S THEOREM  ***
      sumf (%k. k^3) n = (sumf (%k. k) n)^2
   i.e.  0^3 + 1^3 + ... + n^3 = (0 + 1 + ... + n)^2
   Strategy: helper gauss2 (doubling form  add (sumf id n)(sumf id n) = mult n (Suc n))
   then induction on n.  Pure identities on ctxtSub ; reuse the sumf API.
   ============================================================================ *)

val () = out "NICOMACHUS_BEGIN\n";

(* ---- extra mult instantiators on ctxtSub (not named by the foundation) ---- *)
val mult_Suc_vS2        = varify mult_Suc;        (* oeq (mult (Suc m) n)(add n (mult m n)) *)
val mult_Suc_right_vS2N = varify mult_Suc_right;  (* oeq (mult n (Suc m))(add n (mult n m)) *)
val mult_0_vS2N         = varify mult_0;          (* oeq (mult 0 n) 0 *)

fun multSucS2_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_Suc_vS2);
fun multSucrS2_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub nt),(("m",0), ctermSub mt)] mult_Suc_right_vS2N);
fun mult0S2_at t          = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub t)] mult_0_vS2N);

(* identity and cube summand lambdas *)
val idAbs   = Abs("k", natT, Bound 0);                                   (* %k. k *)
val cubeAbs = Abs("k", natT, mult (Bound 0) (mult (Bound 0) (Bound 0))); (* %k. k*(k*k) *)
fun cube_at t = mult t (mult t t);

(* ============================================================================
   HELPER  gauss2 :  oeq (add (sumf idAbs n)(sumf idAbs n)) (mult n (Suc n))
   induction on n.
   ============================================================================ *)
val gauss2 =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT,
          oeq (add (sumf idAbs (Bound 0)) (sumf idAbs (Bound 0)))
              (mult (Bound 0) (suc (Bound 0))));
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  add (sumf id 0)(sumf id 0) = 0 ;  mult 0 (Suc 0) = 0 ---- *)
    val base =
      let
        val sf0  = sumf0_at idAbs;                       (* sumf id 0 = id 0 = 0 [beta] *)
        (* add (sumf id 0)(sumf id 0) = add 0 (sumf id 0) [cong_l] = add 0 0 [cong_r] *)
        val cL   = add_cong_lS2 (sumf idAbs ZeroC, ZeroC, sumf idAbs ZeroC) sf0;
        val cR   = add_cong_rS2 (ZeroC, sumf idAbs ZeroC, ZeroC) sf0;
        val lhs0 = oeq_trans OF [cL, cR];                (* add (sumf id 0)(sumf id 0) = add 0 0 *)
        val a00  = add0S2_at ZeroC;                      (* add 0 0 = 0 *)
        val lhs  = oeq_trans OF [lhs0, a00];             (* LHS = 0 *)
        val rhs  = mult0S2_at (suc ZeroC);               (* mult 0 (Suc 0) = 0 *)
        val rhsS = oeq_sym OF [rhs];                     (* 0 = mult 0 (Suc 0) *)
      in oeq_trans OF [lhs, rhsS] end;

    (* ---- STEP : IH  add S S = mult x (Suc x)  where S = sumf id x ---- *)
    val xF = Free("x", natT);
    val Sx = suc xF;
    val S  = sumf idAbs xF;
    val ihprop = jT (oeq (add S S) (mult xF (suc xF)));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* sumf id (Sx) = add (sumf id x)(id Sx) = add S Sx  [sumf_Suc, beta id Sx = Sx] *)
        val sfS = sumfSuc_at (idAbs, xF);                (* sumf id (Sx) = add S (id$Sx) ; beta -> add S Sx *)
        (* LHS(Sx) = add (sumf id Sx)(sumf id Sx) -> add (add S Sx)(add S Sx) *)
        val cL  = add_cong_lS2 (sumf idAbs Sx, add S Sx, sumf idAbs Sx) sfS;
        val cR  = add_cong_rS2 (add S Sx, sumf idAbs Sx, add S Sx) sfS;
        val lhs1 = oeq_trans OF [cL, cR];                (* = add (add S Sx)(add S Sx) *)
        (* reshuffle (S+Sx)+(S+Sx) -> (S+S)+(Sx+Sx) *)
        val swap = add4_swapS2 (S, Sx, S, Sx);
        val lhs2 = oeq_trans OF [lhs1, swap];            (* = add (add S S)(add Sx Sx) *)
        (* IH on left summand : add S S = mult x Sx *)
        val cIH  = add_cong_lS2 (add S S, mult xF Sx, add Sx Sx) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];             (* = add (mult x Sx)(add Sx Sx) *)
        (* RHS(Sx) = mult Sx (Suc Sx).  mult_Suc_right: = add Sx (mult Sx Sx) *)
        val rS   = multSucrS2_at (Sx, Sx);               (* mult Sx (Suc Sx) = add Sx (mult Sx Sx) *)
        (* mult Sx Sx = mult (Suc x) Sx = add Sx (mult x Sx)  [mult_Suc] *)
        val mss  = multSucS2_at (xF, Sx);                (* mult (Suc x) Sx = add Sx (mult x Sx) *)
        val cR2  = add_cong_rS2 (Sx, mult Sx Sx, add Sx (mult xF Sx)) mss;
        val rhs1 = oeq_trans OF [rS, cR2];               (* RHS = add Sx (add Sx (mult x Sx)) *)
        (* need  lhs3 = rhs1 :  add (mult x Sx)(add Sx Sx) = add Sx (add Sx (mult x Sx)) *)
        (* both are sums of {mult x Sx, Sx, Sx}; reshuffle lhs3 *)
        (* add M (add Sx Sx) -> add (add Sx Sx) M [comm] -> add Sx (add Sx M) [assoc] *)
        val M    = mult xF Sx;
        val cmt  = addcommS2_at (M, add Sx Sx);          (* add M (add Sx Sx) = add (add Sx Sx) M *)
        val asc  = addassocS2_at (Sx, Sx, M);            (* add (add Sx Sx) M = add Sx (add Sx M) *)
        val lhs4 = oeq_trans OF [oeq_trans OF [lhs3, cmt], asc];  (* = add Sx (add Sx M) *)
        val rhs1S= oeq_sym OF [rhs1];                    (* add Sx (add Sx M) = RHS *)
      in oeq_trans OF [lhs4, rhs1S] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val nVn = Var (("n",0), natT);
val i_gauss2 = jT (oeq (add (sumf idAbs nVn) (sumf idAbs nVn)) (mult nVn (suc nVn)));
val r_gauss2 = checkSub ("gauss2", gauss2, i_gauss2);

val gauss2_vN = varify gauss2;
fun gauss2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] gauss2_vN);

(* ============================================================================
   NICOMACHUS :  oeq (sumf cubeAbs n) (mult (sumf idAbs n)(sumf idAbs n))
   induction on n.
   ============================================================================ *)
val nicomachus =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT,
          oeq (sumf cubeAbs (Bound 0))
              (mult (sumf idAbs (Bound 0)) (sumf idAbs (Bound 0))));
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  sumf cube 0 = cube 0 = 0*(0*0) = 0 ;
                          mult (sumf id 0)(sumf id 0) = mult 0 0 = 0 ---- *)
    val base =
      let
        val sc0  = sumf0_at cubeAbs;                     (* sumf cube 0 = cube 0 = mult 0 (mult 0 0) [beta] *)
        (* cube 0 = mult 0 (mult 0 0) ; mult_0 -> 0 *)
        val c0   = mult0S2_at (mult ZeroC ZeroC);        (* mult 0 (mult 0 0) = 0 *)
        val lhs  = oeq_trans OF [sc0, c0];               (* sumf cube 0 = 0 *)
        (* RHS : mult (sumf id 0)(sumf id 0) ; sumf id 0 = 0 *)
        val sf0  = sumf0_at idAbs;                       (* sumf id 0 = 0 *)
        val rcL  = mult_cong_lS2 (sumf idAbs ZeroC, ZeroC, sumf idAbs ZeroC) sf0;
        val rcR  = mult_cong_rS2 (ZeroC, sumf idAbs ZeroC, ZeroC) sf0;
        val rhs0 = oeq_trans OF [rcL, rcR];              (* RHS = mult 0 0 *)
        val m00  = mult0S2_at ZeroC;                     (* mult 0 0 = 0 *)
        val rhs  = oeq_trans OF [rhs0, m00];             (* RHS = 0 *)
        val rhsS = oeq_sym OF [rhs];                     (* 0 = RHS *)
      in oeq_trans OF [lhs, rhsS] end;

    (* ---- STEP : IH  sumf cube x = mult S S   (S = sumf id x) ---- *)
    val xF = Free("x", natT);
    val Sx = suc xF;
    val S  = sumf idAbs xF;
    val ihprop = jT (oeq (sumf cubeAbs xF) (mult S S));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* LHS(Sx) = sumf cube (Sx) = add (sumf cube x)(cube Sx)  [sumf_Suc, beta] *)
        val scS  = sumfSuc_at (cubeAbs, xF);             (* sumf cube (Sx) = add (sumf cube x)(cube Sx) *)
        (* rewrite sumf cube x via IH : -> add (mult S S)(cube Sx) *)
        val cIH  = add_cong_lS2 (sumf cubeAbs xF, mult S S, cube_at Sx) IH;
        val lhs  = oeq_trans OF [scS, cIH];              (* LHS = add (mult S S)(cube Sx) *)

        (* RHS(Sx) = mult (sumf id Sx)(sumf id Sx) ; sumf id Sx = add S Sx *)
        val sfS  = sumfSuc_at (idAbs, xF);               (* sumf id (Sx) = add S Sx [beta] *)
        val U    = add S Sx;
        (* mult (sumf id Sx)(sumf id Sx) -> mult U U *)
        val rcL  = mult_cong_lS2 (sumf idAbs Sx, U, sumf idAbs Sx) sfS;
        val rcR  = mult_cong_rS2 (U, sumf idAbs Sx, U) sfS;
        val rUU  = oeq_trans OF [rcL, rcR];              (* RHS = mult U U *)

        (* expand mult U U : rdist then ldist on each half *)
        val rd   = rdistS2_at (S, Sx, U);                (* mult (add S Sx) U = add (mult S U)(mult Sx U) *)
        val ldL  = ldistS2_at (S, S, Sx);                (* mult S (add S Sx) = add (mult S S)(mult S Sx) *)
        val ldR  = ldistS2_at (Sx, S, Sx);              (* mult Sx (add S Sx) = add (mult Sx S)(mult Sx Sx) *)
        val cExpL= add_cong_lS2 (mult S U, add (mult S S)(mult S Sx), mult Sx U) ldL;
        val cExpR= add_cong_rS2 (add (mult S S)(mult S Sx), mult Sx U, add (mult Sx S)(mult Sx Sx)) ldR;
        val expanded = oeq_trans OF [oeq_trans OF [rd, cExpL], cExpR];
                       (* mult U U = add (add (mult S S)(mult S Sx))(add (mult Sx S)(mult Sx Sx)) *)
        (* pull (mult S S) to the front by assoc :
             add (add A P) Q = add A (add P Q)   A=mult S S, P=mult S Sx, Q=add(mult Sx S)(mult Sx Sx) *)
        val A    = mult S S;
        val P    = mult S Sx;
        val Q    = add (mult Sx S) (mult Sx Sx);
        val asc  = addassocS2_at (A, P, Q);              (* add (add A P) Q = add A (add P Q) *)
        val rExp = oeq_trans OF [expanded, asc];         (* mult U U = add A (add P Q) *)

        (* ---- CUBE identity :  cube Sx = add P Q  ----
           add P Q = add (mult S Sx)(add (mult Sx S)(mult Sx Sx))
           step1: mult S Sx = mult Sx S [mult_comm] -> add (mult Sx S)(add (mult Sx S)(mult Sx Sx))
           step2: add A' (add A' B') = add (add A' A') B' [assoc rev]  A'=mult Sx S, B'=mult Sx Sx
           step3: add A' A' = mult Sx (add S S) [ldist rev] = mult Sx (mult x Sx) [gauss2 at x]
           step4: add (mult Sx (mult x Sx)) (mult Sx Sx) = mult Sx (add (mult x Sx) Sx) [ldist rev]
           step5: add (mult x Sx) Sx = mult Sx Sx -> mult_cong_r -> cube Sx
        *)
        val Ap   = mult Sx S;
        val Bp   = mult Sx Sx;
        (* build  cube Sx = mult Sx (mult Sx Sx)  forward to  add P Q *)
        (* s5: mult Sx Sx = add (mult x Sx) Sx *)
        val mss5 = multSucS2_at (xF, Sx);                (* mult (Suc x) Sx = add Sx (mult x Sx) *)
        val ac5  = addcommS2_at (Sx, mult xF Sx);        (* add Sx (mult x Sx) = add (mult x Sx) Sx *)
        val s5   = oeq_trans OF [mss5, ac5];             (* mult Sx Sx = add (mult x Sx) Sx *)
        (* s4 : cube Sx = mult Sx (mult Sx Sx) -> mult Sx (add (mult x Sx) Sx) [cong_r s5] *)
        val s4   = mult_cong_rS2 (Sx, mult Sx Sx, add (mult xF Sx) Sx) s5;
                   (* cube Sx = mult Sx (add (mult x Sx) Sx) *)
        (* ldist : mult Sx (add (mult x Sx) Sx) = add (mult Sx (mult x Sx))(mult Sx Sx) *)
        val ld4  = ldistS2_at (Sx, mult xF Sx, Sx);
        val s4b  = oeq_trans OF [s4, ld4];               (* cube Sx = add (mult Sx (mult x Sx))(mult Sx Sx) *)
        (* s3 : mult Sx (mult x Sx) = mult Sx (add S S) [cong_r gauss2-sym] = add Ap Ap [ldist] *)
        val g2x  = gauss2_at xF;                         (* add S S = mult x Sx *)
        val g2xS = oeq_sym OF [g2x];                     (* mult x Sx = add S S *)
        val crg  = mult_cong_rS2 (Sx, mult xF Sx, add S S) g2xS;  (* mult Sx (mult x Sx) = mult Sx (add S S) *)
        val ld3  = ldistS2_at (Sx, S, S);                (* mult Sx (add S S) = add (mult Sx S)(mult Sx S) = add Ap Ap *)
        val s3   = oeq_trans OF [crg, ld3];              (* mult Sx (mult x Sx) = add Ap Ap *)
        (* rewrite the left summand of s4b's RHS via s3 :
             add (mult Sx (mult x Sx))(mult Sx Sx) = add (add Ap Ap)(mult Sx Sx) *)
        val s4c  = add_cong_lS2 (mult Sx (mult xF Sx), add Ap Ap, Bp) s3;
        val cubeChain1 = oeq_trans OF [s4b, s4c];        (* cube Sx = add (add Ap Ap) Bp *)
        (* assoc : add (add Ap Ap) Bp = add Ap (add Ap Bp) *)
        val asc2 = addassocS2_at (Ap, Ap, Bp);
        val cubeChain2 = oeq_trans OF [cubeChain1, asc2]; (* cube Sx = add Ap (add Ap Bp) *)
        (* Ap = mult Sx S ; want first Ap -> mult S Sx (= P) via mult_comm *)
        val mc   = multcommS2_at (Sx, S);                (* mult Sx S = mult S Sx = P *)
        val cubeChain3 = oeq_trans OF [cubeChain2,
                           add_cong_lS2 (Ap, P, add Ap Bp) mc];
                         (* cube Sx = add P (add Ap Bp) = add P Q *)
        (* now Q = add Ap Bp = add (mult Sx S)(mult Sx Sx) : matches. cubeChain3 : cube Sx = add P Q *)

        (* add_cong_r on A : add A (cube Sx) = add A (add P Q) *)
        val crAadd = add_cong_rS2 (A, cube_at Sx, add P Q) cubeChain3;
        (* lhs = add A (cube Sx) ; -> add A (add P Q) = mult U U *)
        val lhsToMid = oeq_trans OF [lhs, crAadd];       (* LHS = add A (add P Q) *)
        val rExpS = oeq_sym OF [rExp];                   (* add A (add P Q) = mult U U *)
        val lhsToUU = oeq_trans OF [lhsToMid, rExpS];    (* LHS = mult U U *)
        val rUUS = oeq_sym OF [rUU];                     (* mult U U = RHS *)
      in oeq_trans OF [lhsToUU, rUUS] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_nicomachus =
  jT (oeq (sumf cubeAbs nVn) (mult (sumf idAbs nVn) (sumf idAbs nVn)));
val r_nicomachus = checkSub ("nicomachus", nicomachus, i_nicomachus);

val () = if r_nicomachus then out "OK nicomachus\n" else out "FAILED nicomachus\n";

(* ---- soundness probe : kernel must REJECT a false variant ----
   false claim:  sumf cube n = sumf id n   (drops the squaring)  *)
val nicomachus_false_rejected =
  not ((Thm.prop_of nicomachus) aconv
        (jT (oeq (sumf cubeAbs nVn) (sumf idAbs nVn))));
val () = if nicomachus_false_rejected
         then out "PROBE_OK nicomachus is the squared-sum identity (not the bare sum)\n"
         else out "PROBE_UNSOUND nicomachus collapsed!\n";

val () =
  if r_gauss2 andalso r_nicomachus andalso nicomachus_false_rejected
  then out "NICOMACHUS_OK\n"
  else out "NICOMACHUS_FAILED\n";
(* ============================================================================
   FAULHABER : 6 * sum_{k=0}^n k^2  =  n*(n+1)*(2n+1)
   via a verified Horner-polynomial normalizer over ctxtSub.
   ============================================================================ *)
val () = out "FAULHABER_BEGIN\n";

(* re-varify the multiplication base axioms onto ctxtSub *)
val mult_0_vFB        = varify mult_0;          (* oeq (mult 0 n) 0 *)
val mult_Suc_vFB      = varify mult_Suc;        (* oeq (mult (Suc m) n) (add n (mult m n)) *)
val mult_0_right_vFB  = varify mult_0_right;    (* oeq (mult n 0) 0 *)
val mult_Suc_right_vFB= varify mult_Suc_right;  (* oeq (mult n (Suc m)) (add n (mult n m)) *)

fun mult0FB_at t       = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_vFB);
fun multSucFB_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_Suc_vFB);
fun mult0rFB_at t      = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_right_vFB);
fun multSrFB_at (nt,mt)= beta_norm (Drule.infer_instantiate ctxtSub
                            [(("n",0), ctermSub nt),(("m",0), ctermSub mt)] mult_Suc_right_vFB);
fun add0rFB_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] add_0_right_vS2);

val nVar = Free("x", natT);   (* the induction variable for the step polynomial *)

(* numeral term : Suc-chain over Zero *)
fun numTerm 0 = ZeroC
  | numTerm c = suc (numTerm (c-1));

(* Horner canonical term from a coeff list (low->high) ; we keep lists trimmed *)
fun normTermP [] = ZeroC
  | normTermP [c] = numTerm c
  | normTermP (c::rest) = add (numTerm c) (mult nVar (normTermP rest));

(* trim trailing zeros (so e.g. [4,0] becomes [4], [0] becomes []) *)
fun trimP xs =
  let fun dropz (0::t) = dropz t | dropz t = t
  in rev (dropz (rev xs)) end;

(* ---------- oeq (add (numTerm a)(numTerm b)) (numTerm (a+b)) : walk on b ---------- *)
fun numAdd_pf (a, 0) = add0rFB_at (numTerm a)
  | numAdd_pf (a, b) =
      let
        val asr = addSrS2_at (numTerm a, numTerm (b-1));   (* add a (Suc(b-1)) = Suc(add a (b-1)) *)
        val ih  = numAdd_pf (a, b-1);
        val sc  = Suc_cong OF [ih];
      in oeq_trans OF [asr, sc] end;

(* ---------- oeq (mult (numTerm a)(numTerm b)) (numTerm (a*b)) : walk on a ---------- *)
fun numMul_pf (0, b) = mult0FB_at (numTerm b)
  | numMul_pf (a, b) =
      let
        val ms  = multSucFB_at (numTerm (a-1), numTerm b);
        val ih  = numMul_pf (a-1, b);
        val cR  = add_cong_rS2 (numTerm b, mult (numTerm (a-1)) (numTerm b), numTerm ((a-1)*b)) ih;
        val na  = numAdd_pf (b, (a-1)*b);
      in oeq_trans OF [oeq_trans OF [ms, cR], na] end;

(* ============================================================================
   addNormP : oeq (add (normTermP p1)(normTermP p2)) (normTermP result)
   ============================================================================ *)
fun addNormP ([], ys) = (ys, add0S2_at (normTermP ys))
  | addNormP (xs, []) = (xs, add0rFB_at (normTermP xs))
  | addNormP ([x], [y]) = ([x+y], numAdd_pf (x, y))
  | addNormP ([x], (y::yr)) =
      let
        val Yr = normTermP yr
        val tailT = mult nVar Yr
        val asc = addassocS2_at (numTerm x, numTerm y, tailT)
        val ascS = oeq_sym OF [asc]
        val na = numAdd_pf (x, y)
        val cL = add_cong_lS2 (add (numTerm x)(numTerm y), numTerm (x+y), tailT) na
      in ((x+y)::yr, oeq_trans OF [ascS, cL]) end
  | addNormP ((x::xr), [y]) =
      let
        val Xr = normTermP xr
        val tailT = mult nVar Xr
        val a1 = addassocS2_at (numTerm x, tailT, numTerm y)
        val cc = addcommS2_at (tailT, numTerm y)
        val a1c = add_cong_rS2 (numTerm x, add tailT (numTerm y), add (numTerm y) tailT) cc
        val a2 = addassocS2_at (numTerm x, numTerm y, tailT)
        val a2s = oeq_sym OF [a2]
        val na = numAdd_pf (x, y)
        val cL = add_cong_lS2 (add (numTerm x)(numTerm y), numTerm (x+y), tailT) na
        val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [a1, a1c], a2s], cL]
      in ((x+y)::xr, chain) end
  | addNormP ((x::xr), (y::yr)) =
      let
        val Xr = normTermP xr ; val Yr = normTermP yr
        val tX = mult nVar Xr ; val tY = mult nVar Yr
        val sw = add4_swapS2 (numTerm x, tX, numTerm y, tY)
        val na = numAdd_pf (x, y)
        val (zr, pfZ) = addNormP (xr, yr)
        val ld = ldistS2_at (nVar, Xr, Yr)
        val ldS = oeq_sym OF [ld]
        val cZ = mult_cong_rS2 (nVar, add Xr Yr, normTermP zr) pfZ
        val tXY_norm = oeq_trans OF [ldS, cZ]
        val cAll_l = add_cong_lS2 (add (numTerm x)(numTerm y), numTerm (x+y), add tX tY) na
        val cAll_r = add_cong_rS2 (numTerm (x+y), add tX tY, mult nVar (normTermP zr)) tXY_norm
        val chain = oeq_trans OF [oeq_trans OF [sw, cAll_l], cAll_r]
      in ((x+y)::zr, chain) end;

(* ============================================================================
   scaleNormP c p : oeq (mult (numTerm c) (normTermP p)) (normTermP (map (c* ) p))
   ============================================================================ *)
fun scaleNormP (c, []) = ([], mult0rFB_at (numTerm c))     (* mult c 0 = 0 *)
  | scaleNormP (c, [a]) = ([c*a], numMul_pf (c, a))
  | scaleNormP (c, (a::ar)) =
      let
        val Ar = normTermP ar
        val cT = numTerm c
        val tail = mult nVar Ar
        (* mult c (add a tail) = add (mult c a)(mult c tail)  [left_distrib] *)
        val ld = ldistS2_at (cT, numTerm a, tail)
        (* first term -> numTerm (c*a) *)
        val na = numMul_pf (c, a)
        (* second term mult c (mult n Ar) -> mult n (mult c Ar) :
              mult c (mult n Ar) = mult (mult c n) Ar      [assoc sym]
                                 = mult (mult n c) Ar      [comm cong-l]
                                 = mult n (mult c Ar)      [assoc] *)
        val asc = multassocS2_at (cT, nVar, Ar)             (* (c*n)*Ar = c*(n*Ar) *)
        val ascS = oeq_sym OF [asc]                         (* c*(n*Ar) = (c*n)*Ar *)
        val cm = multcommS2_at (cT, nVar)                   (* c*n = n*c *)
        val cmc = mult_cong_lS2 (mult cT nVar, mult nVar cT, Ar) cm  (* (c*n)*Ar = (n*c)*Ar *)
        val as2 = multassocS2_at (nVar, cT, Ar)             (* (n*c)*Ar = n*(c*Ar) *)
        val sndChain1 = oeq_trans OF [oeq_trans OF [ascS, cmc], as2]  (* c*(n*Ar) = n*(c*Ar) *)
        (* recursively scale Ar *)
        val (sr, pfS) = scaleNormP (c, ar)                  (* oeq (mult c Ar) (normTermP sr) *)
        val cRrec = mult_cong_rS2 (nVar, mult cT Ar, normTermP sr) pfS  (* n*(c*Ar) = n*(normTermP sr) *)
        val sndChain = oeq_trans OF [sndChain1, cRrec]      (* c*(n*Ar) = n*(normTermP sr) *)
        (* combine : add (mult c a)(mult c tail) -> add (numTerm (c*a)) (mult n (normTermP sr)) *)
        val cFst = add_cong_lS2 (mult cT (numTerm a), numTerm (c*a), mult cT tail) na
        val cSnd = add_cong_rS2 (numTerm (c*a), mult cT tail, mult nVar (normTermP sr)) sndChain
        val chain = oeq_trans OF [oeq_trans OF [ld, cFst], cSnd]
      in ((c*a)::sr, chain) end;

val () = out "FAULHABER_SCALE_READY\n";

(* smoke : scale 3 * (poly [1,0,2] = 1 + 2 n^2) -> [3,0,6] *)
val (sc1, sc1pf) = scaleNormP (3, [1,0,2]);
val () = out ("SCALESMOKE poly=[" ^ String.concatWith "," (map Int.toString sc1) ^ "] hyps="
              ^ Int.toString (length (Thm.hyps_of sc1pf)) ^ "\n");

(* ============================================================================
   mulNormP : oeq (mult (normTermP p1)(normTermP p2)) (normTermP result)
   ============================================================================ *)
fun mulNormP ([], p2) = ([], mult0FB_at (normTermP p2))      (* mult 0 Y = 0 *)
  | mulNormP ([c], p2) = scaleNormP (c, p2)                  (* normTermP [c] = numTerm c *)
  | mulNormP ((c::xr), p2) =
      let
        val Y  = normTermP p2
        val Xr = normTermP xr
        val cT = numTerm c
        val tX = mult nVar Xr
        (* mult (add c tX) Y = add (mult c Y)(mult tX Y)   [right_distrib] *)
        val rd = rdistS2_at (cT, tX, Y)
        (* first : mult c Y -> normTermP sP *)
        val (sP, sPpf) = scaleNormP (c, p2)
        (* second : mult (mult n Xr) Y -> mult n (mult Xr Y) -> n * normTermP mP -> shift *)
        val (mP, mPpf) = mulNormP (xr, p2)                   (* oeq (mult Xr Y)(normTermP mP) *)
        val asc = multassocS2_at (nVar, Xr, Y)               (* (n*Xr)*Y = n*(Xr*Y) *)
        val cR  = mult_cong_rS2 (nVar, mult Xr Y, normTermP mP) mPpf  (* n*(Xr*Y) = n*(normTermP mP) *)
        val sndCore = oeq_trans OF [asc, cR]                 (* mult tX Y = n*(normTermP mP) *)
        (* shift : n*(normTermP mP) = normTermP (0::mP)   (when mP nonempty) *)
        val (shifted, sndChain) =
          (case (trimP mP) of
              [] =>
                ([], oeq_trans OF [sndCore, oeqreflS2_at (mult nVar (normTermP mP))])
            | _ =>
                let
                  val a0 = add0S2_at (mult nVar (normTermP mP))   (* oeq (add 0 (n*mP)) (n*mP) *)
                  val a0s = oeq_sym OF [a0]                        (* oeq (n*mP) (add 0 (n*mP)) = normTermP (0::mP) *)
                in (0::mP, oeq_trans OF [sndCore, a0s]) end)
        (* now : add (mult c Y)(mult tX Y) -> add (normTermP sP)(normTermP shifted) -> addNormP *)
        val cFst = add_cong_lS2 (mult cT Y, normTermP sP, mult tX Y) sPpf
        val cSnd = add_cong_rS2 (normTermP sP, mult tX Y, normTermP shifted) sndChain
        val pre = oeq_trans OF [oeq_trans OF [rd, cFst], cSnd]
                  (* oeq (mult (add c tX) Y) (add (normTermP sP)(normTermP shifted)) *)
        val (rP, addpf) = addNormP (sP, shifted)
                  (* oeq (add (normTermP sP)(normTermP shifted)) (normTermP rP) *)
        val chain = oeq_trans OF [pre, addpf]
      in (rP, chain) end;

val () = out "FAULHABER_MULNORM_READY\n";

(* smoke : (1 + n) * (1 + n) = 1 + 2n + n^2 -> [1,2,1] *)
val (mq, mqpf) = mulNormP ([1,1],[1,1]);
val () = out ("MULSMOKE poly=[" ^ String.concatWith "," (map Int.toString mq) ^ "] hyps="
              ^ Int.toString (length (Thm.hyps_of mqpf)) ^ "\n");

(* ============================================================================
   norm : term -> int list * thm    where thm : oeq term (normTermP poly)
   over add/mult/Suc/Zero/numeral/n .  poly is a coeff list (low->high).
   ============================================================================ *)
(* recognize a pure numeral (Suc-chain over Zero) -> SOME c, else NONE *)
fun numOf t =
  if t = ZeroC then SOME 0
  else (case t of (Const _ $ a) =>
                    (case numOf a of SOME c => SOME (c+1) | NONE => NONE)
                | _ => NONE);

(* oeq n (normTermP [0,1]) = oeq n (add Zero (mult n (Suc Zero))) *)
val nVar_norm_pf =
  let
    val msr = multSrFB_at (nVar, ZeroC)            (* mult n (Suc 0) = add n (mult n 0) *)
    val m0  = mult0rFB_at nVar                       (* mult n 0 = 0 *)
    val cr  = add_cong_rS2 (nVar, mult nVar ZeroC, ZeroC) m0  (* add n (mult n 0) = add n 0 *)
    val a0  = add0rFB_at nVar                        (* add n 0 = n *)
    val mn1 = oeq_trans OF [oeq_trans OF [msr, cr], a0]   (* mult n (Suc 0) = n *)
    val mn1s = oeq_sym OF [mn1]                      (* n = mult n (Suc 0) *)
    val a0z = add0S2_at (mult nVar (suc ZeroC))      (* add 0 (mult n (Suc 0)) = mult n (Suc 0) *)
    val a0zs = oeq_sym OF [a0z]                       (* mult n (Suc 0) = add 0 (mult n (Suc 0)) *)
  in oeq_trans OF [mn1s, a0zs] end;

fun norm t =
  (case numOf t of
      SOME c => ([c], oeqreflS2_at t)               (* normTermP [c] = numTerm c = t *)
    | NONE =>
      if t = nVar then ([0,1], nVar_norm_pf)
      else
        (case t of
            (f $ a $ b) =>
              if f = addC then
                let
                  val (pa, pfa) = norm a
                  val (pb, pfb) = norm b
                  val cl = add_cong_lS2 (a, normTermP pa, b) pfa
                  val cr = add_cong_rS2 (normTermP pa, b, normTermP pb) pfb
                  val cong = oeq_trans OF [cl, cr]
                  val (rP, addpf) = addNormP (pa, pb)
                in (rP, oeq_trans OF [cong, addpf]) end
              else if f = multC then
                let
                  val (pa, pfa) = norm a
                  val (pb, pfb) = norm b
                  val cl = mult_cong_lS2 (a, normTermP pa, b) pfa
                  val cr = mult_cong_rS2 (normTermP pa, b, normTermP pb) pfb
                  val cong = oeq_trans OF [cl, cr]
                  val (rP, mulpf) = mulNormP (pa, pb)
                in (rP, oeq_trans OF [cong, mulpf]) end
              else raise Fail "norm: unknown binary head"
          | (Const _ $ a) =>   (* Suc of a non-numeral *)
              let
                val asr = addSrS2_at (a, ZeroC)         (* add a (Suc 0) = Suc(add a 0) *)
                val a0  = add0rFB_at a                   (* add a 0 = a *)
                val sc  = Suc_cong OF [a0]               (* Suc(add a 0) = Suc a *)
                val sia = oeq_sym OF [oeq_trans OF [asr, sc]]  (* Suc a = add a (Suc 0) *)
                val (pa, pfa) = norm a
                val cl = add_cong_lS2 (a, normTermP pa, suc ZeroC) pfa
                val cr = add_cong_rS2 (normTermP pa, suc ZeroC, numTerm 1) (oeqreflS2_at (suc ZeroC))
                val cong = oeq_trans OF [cl, cr]
                val (rP, addpf) = addNormP (pa, [1])
              in (rP, oeq_trans OF [oeq_trans OF [sia, cong], addpf]) end
          | _ => raise Fail "norm: leaf not handled"));

val () = out "FAULHABER_NORM_READY\n";

(* smoke : norm ((Suc n)*(Suc n)) -> [1,2,1] *)
val (nq, nqpf) = norm (mult (suc nVar) (suc nVar));
val () = out ("NORMSMOKE poly=[" ^ String.concatWith "," (map Int.toString nq) ^ "] hyps="
              ^ Int.toString (length (Thm.hyps_of nqpf)) ^ "\n");

(* ============================================================================
   THE MAIN PROOF : 6 * sumf (%k. k*k) n = n*(Suc n)*(Suc(2n))
   induction on n (variable nVar = Free "x" so the step polynomial uses x).
   ============================================================================ *)
val sixT = numTerm 6;
val twoT = numTerm 2;
val fAbs = Abs("k", natT, mult (Bound 0) (Bound 0));   (* %k. mult k k *)
fun fSq t = mult t t;                                   (* f t after beta *)
fun rhsT u = mult u (mult (suc u) (suc (mult twoT u))); (* n*(Sn)*(S(2n)) *)

(* polyEq A B : given A, B pure x-polynomials, produce oeq A B by normalizing both *)
fun polyEq (A, B) =
  let
    val (pa, pfa) = norm A          (* oeq A (normTermP pa) *)
    val (pb, pfb) = norm B          (* oeq B (normTermP pb) *)
    val () = if trimP pa = trimP pb then ()
             else raise Fail ("polyEq mismatch: [" ^ String.concatWith "," (map Int.toString pa)
                              ^ "] vs [" ^ String.concatWith "," (map Int.toString pb) ^ "]")
  in oeq_trans OF [pfa, oeq_sym OF [pfb]] end;          (* oeq A B *)

val faulhaber_sq =
  let
    val Qpred = Abs("z", natT, oeq (mult sixT (sumf fAbs (Bound 0))) (rhsT (Bound 0)));
    val nF = nVar;                                       (* Free "x" *)
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  6 * sumf f 0 = 6 * (f 0) = 6 * 0 = 0 ; rhsT 0 = 0*...=0 ---- *)
    val base =
      let
        val sf0 = sumf0_at fAbs;                         (* sumf f 0 = f 0 = mult 0 0 [beta] *)
        val cL  = mult_cong_rS2 (sixT, sumf fAbs ZeroC, fSq ZeroC) sf0;  (* 6 * sumf f 0 = 6 * (0*0) *)
        (* 0*0 = 0 *)
        val z00 = mult0FB_at ZeroC;                      (* mult 0 0 = 0 *)
        val cL2 = mult_cong_rS2 (sixT, fSq ZeroC, ZeroC) z00;  (* 6*(0*0) = 6*0 *)
        val m60 = mult0rFB_at sixT;                      (* 6*0 = 0 *)
        val lhs0 = oeq_trans OF [oeq_trans OF [cL, cL2], m60];   (* 6 * sumf f 0 = 0 *)
        (* rhsT 0 = mult 0 (...) = 0 *)
        val r0  = mult0FB_at (mult (suc ZeroC) (suc (mult twoT ZeroC)));  (* mult 0 X = 0 *)
        val r0s = oeq_sym OF [r0];                        (* 0 = rhsT 0 *)
      in oeq_trans OF [lhs0, r0s] end;

    (* ---- STEP ---- *)
    val xF = nVar;
    val ihprop = jT (oeq (mult sixT (sumf fAbs xF)) (rhsT xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* sumf f (Suc x) = add (sumf f x)(f (Suc x)) ; f (Suc x) = mult (Suc x)(Suc x) [beta] *)
        val sfS = sumfSuc_at (fAbs, xF);                 (* sumf f (Sx) = add (sumf f x)(mult (Sx)(Sx)) *)
        val cMul = mult_cong_rS2 (sixT, sumf fAbs (suc xF), add (sumf fAbs xF) (fSq (suc xF))) sfS;
                   (* 6 * sumf f (Sx) = 6 * (add (sumf f x)(Sx*Sx)) *)
        val ld = ldistS2_at (sixT, sumf fAbs xF, fSq (suc xF));
                   (* 6*(add A B) = add (6*A)(6*B) *)
        val lhs1 = oeq_trans OF [cMul, ld];
                   (* 6 * sumf f (Sx) = add (6 * sumf f x)(6*(Sx*Sx)) *)
        (* apply IH to left summand *)
        val cIH = add_cong_lS2 (mult sixT (sumf fAbs xF), rhsT xF, mult sixT (fSq (suc xF))) IH;
                   (* add (6*sumf f x)(6*(Sx*Sx)) = add (rhsT x)(6*(Sx*Sx)) *)
        val lhs2 = oeq_trans OF [lhs1, cIH];
                   (* 6 * sumf f (Sx) = add (rhsT x)(6*(Sx*Sx)) *)
        (* now pure polynomial identity : add (rhsT x)(6*(Sx*Sx)) = rhsT (Suc x) *)
        val Aterm = add (rhsT xF) (mult sixT (fSq (suc xF)));
        val Bterm = rhsT (suc xF);
        val polyeq = polyEq (Aterm, Bterm);              (* oeq A B *)
      in oeq_trans OF [lhs2, polyeq] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* intended statement (schematic ?x, matching varify of Free "x") on ctxtSub *)
val xVs = Var (("x",0), natT);
val i_faulhaber_sq =
  jT (oeq (mult (numTerm 6) (sumf fAbs xVs)) (mult xVs (mult (suc xVs) (suc (mult (numTerm 2) xVs)))));
val r_faulhaber_sq = checkSub ("faulhaber_sq", faulhaber_sq, i_faulhaber_sq);

val () = if r_faulhaber_sq then out "OK faulhaber_sq\n" else out "FAIL faulhaber_sq\n";

(* soundness probe : the kernel must REJECT a false variant (drop the +1 in 2n+1) *)
val probe_ok =
  let
    val bogus = jT (oeq (mult (numTerm 6) (sumf fAbs xVs)) (mult xVs (mult (suc xVs) (mult (numTerm 2) xVs))));
  in not ((Thm.prop_of faulhaber_sq) aconv bogus) end;
val () = out ("SOUNDNESS_PROBE faulhaber_sq rejects-false=" ^ Bool.toString probe_ok ^ "\n");

val () = if r_faulhaber_sq andalso probe_ok then out "FAULHABER_SQ_OK\n"
         else out "FAULHABER_SQ_FAIL\n";
(* ============================================================================
   PRONIC / TRIANGULAR-PRODUCT SUM  (seat pronic_sum0)
     3 * (0*1 + 1*2 + ... + n*(n+1)) = n*(n+1)*(n+2)
   i.e.  mult 3 (sumf (%k. mult k (Suc k)) n) = mult n (mult (Suc n)(Suc(Suc n)))
   Proof by induction on n, routed entirely through ctxtSub / ctermSub.
   ============================================================================ *)

val () = out "PRONIC_BEGIN\n";

(* ---- varify the mult base axioms onto ctxtSub + ground instantiators ---- *)
val mult_0_vS2        = varify mult_0;          (* oeq (mult Zero n) Zero          *)
val mult_Suc_vS2      = varify mult_Suc;        (* oeq (mult (Suc m) n)(add n (mult m n)) *)
val mult_0_right_vS2  = varify mult_0_right;    (* oeq (mult n Zero) Zero          *)
val mult_Suc_right_vS2= varify mult_Suc_right;  (* oeq (mult n (Suc m))(add n (mult n m)) *)

fun mult0S2_at t        = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_vS2);
fun mult0rS2_at t       = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_right_vS2);
fun multSucS2_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_Suc_vS2);

(* ---- the constant 3 and the summand lambda  %k. mult k (Suc k) ---- *)
val three = suc (suc (suc ZeroC));
val summandAbs = Abs("k", natT, mult (Bound 0) (suc (Bound 0)));
fun summand_at t = mult t (suc t);          (* what summandAbs $ t beta-reduces to *)

(* convenience : LHS / RHS shapes at a term z *)
fun lhsAt z = mult three (sumf summandAbs z);
fun rhsAt z = mult z (mult (suc z) (suc (suc z)));

val pronic_sum =
  let
    val nF = Free("n", natT);
    val xF = Free("x", natT);

    val Qpred = Abs("z", natT,
        oeq (mult three (sumf summandAbs (Bound 0)))
            (mult (Bound 0) (mult (suc (Bound 0)) (suc (suc (Bound 0))))));

    val ind = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Qpred), (("k",0), ctermSub nF)] nat_induct_vS2);

    (* ---------------- BASE  n = 0 ---------------------------------------
       LHS = mult 3 (sumf summand 0)
           = mult 3 (mult 0 (Suc 0))            [sumf_0, beta]
           = mult 3 0                           [mult_0]
           = 0                                  [mult_0_right]
       RHS = mult 0 (mult (Suc 0)(Suc(Suc 0))) = 0   [mult_0]            *)
    val base =
      let
        val sf0   = sumf0_at summandAbs;                 (* sumf summand 0 = mult 0 (Suc 0) *)
        val m0s0  = mult0S2_at (suc ZeroC);              (* mult 0 (Suc 0) = 0 *)
        val sf0z  = oeq_trans OF [sf0, m0s0];            (* sumf summand 0 = 0 *)
        val cL1   = mult_cong_rS2 (three, sumf summandAbs ZeroC, ZeroC) sf0z;
                                                         (* mult 3 (sumf summand 0) = mult 3 0 *)
        val m3z   = mult0rS2_at three;                   (* mult 3 0 = 0 *)
        val lhs0  = oeq_trans OF [cL1, m3z];             (* LHS(0) = 0 *)
        val rhs0  = mult0S2_at (mult (suc ZeroC) (suc (suc ZeroC)));
                                                         (* mult 0 (..) = 0 *)
        val rhs0s = oeq_sym OF [rhs0];                   (* 0 = RHS(0) *)
      in oeq_trans OF [lhs0, rhs0s] end;                 (* LHS(0) = RHS(0) *)

    (* ---------------- STEP  n = Suc x ----------------------------------- *)
    val ihprop = jT (oeq (lhsAt xF) (rhsAt xF));
    val IH = Thm.assume (ctermSub ihprop);              (* mult 3 (sumf summand x) = mult x (mult (Sx)(SSx)) *)

    val step =
      let
        (* abbreviations *)
        val Sx   = suc xF;
        val SSx  = suc (suc xF);
        val SSSx = suc (suc (suc xF));
        val P    = mult Sx SSx;                         (* (Suc x)*(Suc(Suc x)) *)

        (* sumf summand (Suc x) = add (sumf summand x) (summand (Suc x))
                                = add (sumf summand x) (mult Sx SSx)    [beta] *)
        val sfS  = sumfSuc_at (summandAbs, xF);
        (* mult 3 (sumf summand (Sx)) = mult 3 (add (sumf summand x) P) *)
        val cL   = mult_cong_rS2 (three, sumf summandAbs Sx, add (sumf summandAbs xF) P) sfS;
        (* left_distrib : mult 3 (add A B) = add (mult 3 A)(mult 3 B) *)
        val ld   = ldistS2_at (three, sumf summandAbs xF, P);
        (* now = add (mult 3 (sumf summand x)) (mult 3 P) *)
        val lchain1 = oeq_trans OF [cL, ld];
        (* IH : mult 3 (sumf summand x) = mult x P  (note rhsAt x = mult x P) *)
        (* rewrite the FIRST summand of the add via IH : add (mult 3 (sumf summand x)) (mult 3 P)
                                                        = add (mult x P) (mult 3 P) *)
        val cIH  = add_cong_lS2 (mult three (sumf summandAbs xF), rhsAt xF, mult three P) IH;
        val lchain2 = oeq_trans OF [lchain1, cIH];
        (* LHS(Sx) = add (mult x (mult Sx SSx)) (mult 3 (mult Sx SSx))
                   = add (mult x P) (mult 3 P)   (since rhsAt x = mult x P) *)

        (* combine via right_distrib backwards :
             add (mult x P)(mult 3 P) = mult (add x 3) P                  *)
        val rdist = rdistS2_at (xF, three, P);          (* mult (add x 3) P = add (mult x P)(mult 3 P) *)
        val rdistS = oeq_sym OF [rdist];                (* add (mult x P)(mult 3 P) = mult (add x 3) P *)
        val lchain3 = oeq_trans OF [lchain2, rdistS];   (* LHS(Sx) = mult (add x 3) P *)

        (* add x 3 = Suc(Suc(Suc x)) :  add x (Suc(Suc(Suc 0))) *)
        val a1 = addSrS2_at (xF, suc (suc ZeroC));       (* add x (S(S(S0))) = S(add x (S(S0))) *)
        val a2 = addSrS2_at (xF, suc ZeroC);             (* add x (S(S0))   = S(add x (S0))   *)
        val a3 = addSrS2_at (xF, ZeroC);                 (* add x (S0)      = S(add x 0)      *)
        val a4 = add0rS2_at xF;                          (* add x 0 = x *)
        (* build  add x 3 = S(S(S x))  by chaining congruences under Suc *)
        val c4  = Suc_cong OF [a4];                       (* S(add x 0) = S x *)
        val c3  = oeq_trans OF [a3, c4];                  (* add x (S0) = S x *)
        val c3s = Suc_cong OF [c3];                       (* S(add x (S0)) = S(S x) *)
        val c2  = oeq_trans OF [a2, c3s];                 (* add x (S(S0)) = S(S x) *)
        val c2s = Suc_cong OF [c2];                       (* S(add x (S(S0))) = S(S(S x)) *)
        val addx3 = oeq_trans OF [a1, c2s];              (* add x 3 = S(S(S x)) = SSSx *)

        (* mult (add x 3) P = mult SSSx P  by left congruence *)
        val cFac = mult_cong_lS2 (add xF three, SSSx, P) addx3;   (* mult (add x 3) P = mult SSSx P *)
        val lchain4 = oeq_trans OF [lchain3, cFac];      (* LHS(Sx) = mult SSSx P = mult SSSx (mult Sx SSx) *)

        (* rearrange  mult SSSx (mult Sx SSx)  ->  mult Sx (mult SSx SSSx)  = RHS(Sx)
             mult C (mult A B)  =  mult (mult A B) C   [comm]
                                =  mult A (mult B C)   [assoc]
           with A=Sx, B=SSx, C=SSSx *)
        val cm   = multcommS2_at (SSSx, mult Sx SSx);    (* mult SSSx (mult Sx SSx) = mult (mult Sx SSx) SSSx *)
        val asc  = multassocS2_at (Sx, SSx, SSSx);       (* mult (mult Sx SSx) SSSx = mult Sx (mult SSx SSSx) *)
        val rearr = oeq_trans OF [cm, asc];              (* mult SSSx (mult Sx SSx) = mult Sx (mult SSx SSSx) *)
        val lchain5 = oeq_trans OF [lchain4, rearr];     (* LHS(Sx) = mult Sx (mult SSx SSSx) = RHS(Sx) *)

        (* RHS(Sx) = mult (Suc x) (mult (Suc(Suc x)) (Suc(Suc(Suc x)))) -- exactly lchain5's RHS *)
      in lchain5 end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) step);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ---- intended statement, schematic on ctxtSub ---- *)
val i_pronic_sum =
  jT (oeq (mult three (sumf summandAbs nVs))
          (mult nVs (mult (suc nVs) (suc (suc nVs)))));
val r_pronic_sum = checkSub ("pronic_sum", pronic_sum, i_pronic_sum);

(* ---- soundness probe : the kernel must REJECT a false variant.
   The false statement drops the final factor (Suc(Suc n)) -> claims
   3*sum = n*(Suc n).  Our proved theorem must NOT be aconv to it. *)
val i_pronic_false =
  jT (oeq (mult three (sumf summandAbs nVs))
          (mult nVs (suc nVs)));
val pronic_not_false = not ((Thm.prop_of pronic_sum) aconv i_pronic_false);

val () =
  if r_pronic_sum andalso pronic_not_false
  then out "PRONIC_SOUNDPROBE_OK\n"
  else out "PRONIC_SOUNDPROBE_FAIL\n";

val () =
  if r_pronic_sum andalso pronic_not_false
  then out "PRONIC_OK\n"
  else out "PRONIC_FAILED\n";
