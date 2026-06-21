(* ============================================================================
   BRAHMAGUPTA-FIBONACCI IDENTITY in Isabelle/Pure on the polyml-rs interpreter.
   (graceful-floor lemma #1 for the full Fermat two-square iff campaign)
   ----------------------------------------------------------------------------
   The product of two sums of two squares is a sum of two squares:

     (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2
                               [ = (a*c + b*d)^2 + (a*d - b*c)^2 ]

   Over the truncated naturals N, (a*c - b*d) is only the "right" cross term
   when b*d <= a*c (and symmetrically), so the LITERAL `sub` form is FALSE when
   the wrong side is bigger (e.g. a=c=0, b=d=1: LHS=1, RHS=(0-1)^2+0=0).  The
   FAITHFUL 0-hyp statement is therefore the sum-PRESERVATION existential

     brahmagupta : |- Ex P. Ex Q. oeq ((a^2+b^2)*(c^2+d^2)) (P^2 + Q^2)

   i.e. "the product is a sum of two squares", which is what the two-square
   merge actually needs (four_sq_mult-style multiplicativity).  Q = a*d + b*c
   (always positive); P = |a*c - b*d| is produced by a le_total case-split, with
   the truncated subtraction handled exactly as four_sq_mult's sq_diff trick:
   for the positive cross product P0=a*c, Q0=b*d there is s = |a*c - b*d| with
   s^2 + 2*(a*c)*(b*d) = (a*c)^2 + (b*d)^2 (an all-positive identity), and then
   the whole identity holds after cancelling the common term 2*(a*c)*(b*d).

   Built on common::with_nt_helpers (the classical NT foundation).  Final
   context = ctxtC / ctermC.  NO new constants, NO new axioms; only classical
   assumption inherited = excluded middle (not even used here).  0-hyp, aconv
   the intended statement, with a soundness probe.
   ============================================================================ *)

val () = out "BRAHMA_DELTA_BEGIN\n";

(* ---------------------------------------------------------------------------
   ALGEBRA TOOLKIT on ctxtC (varify the semiring lemmas; ground instantiators
   + congruence helpers).  Mirrors isabelle_sqrt2.sml's ctxtC setup.
   --------------------------------------------------------------------------- *)
val left_distrib_vCb  = varify left_distrib;
val right_distrib_vCb = varify right_distrib;
val mult_assoc_vCb    = varify mult_assoc;
val mult_comm_vCb     = varify mult_comm;
val add_assoc_vCb     = varify add_assoc;
val add_comm_vCb      = varify add_comm;
val add_left_cancel_vCb = varify add_left_cancel;

fun left_distrib_atC (xT, mT, nT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("x",0), ctermC xT), (("m",0), ctermC mT), (("n",0), ctermC nT)] left_distrib_vCb);
fun right_distrib_atC (mT, nT, kT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mT), (("n",0), ctermC nT), (("k",0), ctermC kT)] right_distrib_vCb);
fun mult_assoc_atC (mT, nT, kT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mT), (("n",0), ctermC nT), (("k",0), ctermC kT)] mult_assoc_vCb);
fun mult_comm_atC (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt)] mult_comm_vCb);
fun add_assoc_atC (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt),(("k",0), ctermC kt)] add_assoc_vCb);
fun add_comm_atC (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt)] add_comm_vCb);

(* mult-congruence on LEFT / RIGHT operand, on ctxtC *)
fun mult_cong_lC (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rC (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;

(* convenient aliases that match the partA `_g` toolkit names so the polynomial
   normalizer ports verbatim *)
fun oeqRefl_g t = oeqreflC_at t;
fun oeqTrans_g (h1,h2) = oeq_trans OF [h1,h2];
fun oeqSym_g h = oeq_sym OF [h];
fun mult_cong_l_g (s,sN,u) h = mult_cong_lC (s,sN,u) h;
fun mult_cong_r_g (s,u,uN) h = mult_cong_rC (s,u,uN) h;
fun add_cong_l_g (s,sN,u) h = add_cong_lC (s,sN,u) h;
fun add_cong_r_g (s,u,uN) h = add_cong_rC (s,u,uN) h;
fun multassoc_g (x,y,v) = mult_assoc_atC (x,y,v);
fun addassoc_g (x,y,v) = add_assoc_atC (x,y,v);
fun multcomm_g (x,y) = mult_comm_atC (x,y);
fun addcomm_g (x,y) = add_comm_atC (x,y);
fun leftdistrib_g (m,n,k) = left_distrib_atC (m,n,k);
fun rightdistrib_g (m,n,k) = right_distrib_atC (m,n,k);

val () = out "BRAHMA_TOOLKIT_READY\n";

(* ---------------------------------------------------------------------------
   POLYNOMIAL NORMALIZER (ported verbatim from four_square_resume/
   partA_identity_delta.sml; uses only the _g toolkit above).
   proveIdentityG L R : |- oeq L R for an all-positive (no-sub) polynomial
   identity (both sides canonicalize to the same monomial multiset).
   --------------------------------------------------------------------------- *)
fun atomKey (Free(n,_)) = n
  | atomKey _ = "~";
val addName  = #1 (Term.dest_Const addC);
val multName = #1 (Term.dest_Const multC);
fun destAdd  (Const(n,_) $ s $ t) = if n=addName then SOME(s,t) else NONE
  | destAdd _ = NONE;
fun destMult (Const(n,_) $ s $ t) = if n=multName then SOME(s,t) else NONE
  | destMult _ = NONE;

fun monOf [x] = x
  | monOf (x::xs) = mult x (monOf xs)
  | monOf [] = raise Fail "monOf empty";
fun polyOf [m] = m
  | polyOf (m::ms) = add m (polyOf ms)
  | polyOf [] = raise Fail "polyOf empty";

fun flattenMult t =
  case destMult t of SOME(s,u) => flattenMult s @ flattenMult u | NONE => [t];

fun monoReassoc t =
  case destMult t of
      NONE => oeqRefl_g t
    | SOME(s,u) =>
        let
          val fs = flattenMult s
          val fu = flattenMult u
          val hs = monoReassoc s
          val hu = monoReassoc u
          val sN = monOf fs
          val uN = monOf fu
          val step1 = oeqTrans_g (mult_cong_l_g (s, sN, u) hs,
                                  mult_cong_r_g (sN, u, uN) hu)
          fun reassocCat ([x], v) = oeqRefl_g (mult x v)
            | reassocCat (x::xs, v) =
                let val inner = reassocCat (xs, v)
                    val assoc = multassoc_g (x, monOf xs, v)
                in oeqTrans_g (assoc, mult_cong_r_g (x, mult (monOf xs) v, monOf (xs @ fu)) inner) end
            | reassocCat ([], v) = oeqRefl_g v
          val catEq = reassocCat (fs, uN)
        in oeqTrans_g (step1, catEq) end;

fun monoCommHead (x, y, rest) =
  case rest of
      [] => multcomm_g (x, y)
    | _  =>
        let val v = monOf rest
            val a1 = oeqSym_g (multassoc_g (x, y, v))
            val c1 = mult_cong_l_g (mult x y, mult y x, v) (multcomm_g (x,y))
            val a2 = multassoc_g (y, x, v)
        in oeqTrans_g (oeqTrans_g (a1, c1), a2) end;

fun monoInsert x [] = oeqRefl_g x
  | monoInsert x (y::ys) =
      if String.compare(atomKey x, atomKey y) <> GREATER
      then oeqRefl_g (monOf (x::y::ys))
      else
        let
          val swap = monoCommHead (x, y, ys)
          val rec0 = monoInsert x ys
          val ins  = insertSorted x ys
          val congr =
            (case ys of
                 [] => oeqRefl_g (monOf (y :: x :: ys))
               | _  => mult_cong_r_g (y, monOf (x::ys), monOf ins) rec0)
        in oeqTrans_g (swap, congr) end
and insertSorted x [] = [x]
  | insertSorted x (y::ys) =
      if String.compare(atomKey x, atomKey y) <> GREATER then x::y::ys
      else y :: insertSorted x ys;

fun sortAtoms [] = []
  | sortAtoms (x::xs) = insertSorted x (sortAtoms xs);
fun monoSort [] = raise Fail "monoSort empty"
  | monoSort [x] = oeqRefl_g x
  | monoSort (x::xs) =
      let
        val hxs = monoSort xs
        val sx  = sortAtoms xs
        val step1 = mult_cong_r_g (x, monOf xs, monOf sx) hxs
        val ins   = monoInsert x sx
      in oeqTrans_g (step1, ins) end;

fun normMono t =
  let val hr = monoReassoc t
      val fl = flattenMult t
      val hs = monoSort fl
  in oeqTrans_g (hr, hs) end;

fun monoCmp (m1, m2) =
  let val k1 = flattenMult m1 val k2 = flattenMult m2
      fun go ([],[]) = EQUAL | go ([],_) = LESS | go (_,[]) = GREATER
        | go (x::xs,y::ys) = (case String.compare(atomKey x, atomKey y) of EQUAL => go(xs,ys) | c => c)
  in go (k1,k2) end;

fun appendProof ([a], Bs) = oeqRefl_g (add a (polyOf Bs))
  | appendProof (a::As, Bs) =
      let
        val rest = appendProof (As, Bs)
        val assoc = addassoc_g (a, polyOf As, polyOf Bs)
        val congr = add_cong_r_g (a, add (polyOf As) (polyOf Bs), polyOf (As @ Bs)) rest
      in oeqTrans_g (assoc, congr) end
  | appendProof ([], Bs) = oeqRefl_g (polyOf Bs);

fun addCommHead (x, y, rest) =
  case rest of
      [] => addcomm_g (x, y)
    | _  =>
        let val v = polyOf rest
            val a1 = oeqSym_g (addassoc_g (x, y, v))
            val c1 = add_cong_l_g (add x y, add y x, v) (addcomm_g (x,y))
            val a2 = addassoc_g (y, x, v)
        in oeqTrans_g (oeqTrans_g (a1, c1), a2) end;

fun polyInsert x [] = oeqRefl_g x
  | polyInsert x (y::ys) =
      if monoCmp(x,y) <> GREATER
      then oeqRefl_g (polyOf (x::y::ys))
      else
        let
          val swap = addCommHead (x, y, ys)
          val rec0 = polyInsert x ys
          val ins  = pInsertSorted x ys
          val congr =
            (case ys of
                 [] => oeqRefl_g (polyOf (y :: x :: ys))
               | _  => add_cong_r_g (y, polyOf (x::ys), polyOf ins) rec0)
        in oeqTrans_g (swap, congr) end
and pInsertSorted x [] = [x]
  | pInsertSorted x (y::ys) =
      if monoCmp(x,y) <> GREATER then x::y::ys else y :: pInsertSorted x ys;

fun pSortList [] = []
  | pSortList (x::xs) = pInsertSorted x (pSortList xs);
fun polySort [] = raise Fail "polySort empty"
  | polySort [x] = oeqRefl_g x
  | polySort (x::xs) =
      let
        val hxs = polySort xs
        val sx  = pSortList xs
        val step1 = add_cong_r_g (x, polyOf xs, polyOf sx) hxs
        val ins   = polyInsert x sx
      in oeqTrans_g (step1, ins) end;

fun mulMonoPoly m [n] = oeqRefl_g (mult m n)
  | mulMonoPoly m (n::ns) =
      let
        val ld = leftdistrib_g (m, n, polyOf ns)
        val rec0 = mulMonoPoly m ns
        val congr = add_cong_r_g (mult m n, mult m (polyOf ns), polyOf (map (fn x => mult m x) ns)) rec0
      in oeqTrans_g (ld, congr) end
  | mulMonoPoly _ [] = raise Fail "mulMonoPoly empty";

fun mulPolyPoly [m] Bs = mulMonoPoly m Bs
  | mulPolyPoly (m::ms) Bs =
      let
        val rd = rightdistrib_g (m, polyOf ms, polyOf Bs)
        val left = mulMonoPoly m Bs
        val rec0 = mulPolyPoly ms Bs
        val msProd = List.concat (map (fn mm => map (fn n => mult mm n) Bs) ms)
        val mProd  = map (fn n => mult m n) Bs
        val c1 = add_cong_l_g (mult m (polyOf Bs), polyOf mProd, mult (polyOf ms) (polyOf Bs)) left
        val c2 = add_cong_r_g (polyOf mProd, mult (polyOf ms) (polyOf Bs), polyOf msProd) rec0
        val step = oeqTrans_g (oeqTrans_g (rd, c1), c2)
        val ap = appendProof (mProd, msProd)
      in oeqTrans_g (step, ap) end
  | mulPolyPoly [] _ = raise Fail "mulPolyPoly empty";

fun canonOf m = monOf (sortAtoms (flattenMult m));
fun normMonoListEq [m] = normMono m
  | normMonoListEq (m::ms) =
      let
        val hm = normMono m
        val rec0 = normMonoListEq ms
        val cm = canonOf m
        val c1 = add_cong_l_g (m, cm, polyOf ms) hm
        val c2 = add_cong_r_g (cm, polyOf ms, polyOf (map canonOf ms)) rec0
      in oeqTrans_g (c1, c2) end
  | normMonoListEq [] = raise Fail "normMonoListEq empty";

fun normPolyFull t =
  case destAdd t of
      SOME(s,u) =>
        let
          val (hs, Ms) = normPolyFull s
          val (hu, Ns) = normPolyFull u
          val c1 = add_cong_l_g (s, polyOf Ms, u) hs
          val c2 = add_cong_r_g (polyOf Ms, u, polyOf Ns) hu
          val merged = oeqTrans_g (c1, c2)
          val ap = appendProof (Ms, Ns)
          val cat = Ms @ Ns
          val srt = polySort cat
          val sortedList = pSortList cat
          val full = oeqTrans_g (oeqTrans_g (merged, ap), srt)
        in (full, sortedList) end
    | NONE =>
        (case destMult t of
             SOME(s,u) =>
               let
                 val (hs, Ms) = normPolyFull s
                 val (hu, Ns) = normPolyFull u
                 val c1 = mult_cong_l_g (s, polyOf Ms, u) hs
                 val c2 = mult_cong_r_g (polyOf Ms, u, polyOf Ns) hu
                 val prodEq = oeqTrans_g (c1, c2)
                 val mul = mulPolyPoly Ms Ns
                 val rawProds = List.concat (map (fn mm => map (fn n => mult mm n) Ns) Ms)
                 val nm = normMonoListEq rawProds
                 val canonList = map canonOf rawProds
                 val srt = polySort canonList
                 val sortedList = pSortList canonList
                 val full = oeqTrans_g (oeqTrans_g (oeqTrans_g (prodEq, mul), nm), srt)
               in (full, sortedList) end
           | NONE =>
               let val h = normMono t in (h, [canonOf t]) end);

fun proveIdentityG L R =
  let
    val (hL, msL) = normPolyFull L
    val (hR, msR) = normPolyFull R
    val cL = polyOf msL
    val cR = polyOf msR
    val () = if (cL aconv cR) then ()
             else raise Fail ("IDENTITY MISMATCH\nL canon="^Syntax.string_of_term ctxtC cL^
                              "\nR canon="^Syntax.string_of_term ctxtC cR)
  in oeqTrans_g (hL, oeqSym_g hR) end;

val () = out "BRAHMA_NORMALIZER_READY\n";

(* smoke: (a+b)*c = c*a + c*b *)
val () =
  let
    val aa = Free("a_sm",natT); val bb = Free("b_sm",natT); val cc = Free("c_sm",natT)
    val L = mult (add aa bb) cc
    val R = add (mult cc aa) (mult cc bb)
    val h = proveIdentityG L R
  in out ("SMOKE proveIdentityG hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE proveIdentityG FAIL "^exnMessage e^"\n");

(* ---------------------------------------------------------------------------
   sq_diff_law (P,Q) : |- Ex s. oeq (add (s^2) (2*(P*Q))) (add (P^2) (Q^2))
   "there is s = |P - Q| with s^2 + 2*P*Q = P^2 + Q^2 (over N)".
   Proof by le_total on (P,Q):
     case le Q P : witness s with P = Q + s (le_total gives the witness via exE);
        proveIdentityG: s^2 + 2*(Q+s)*Q = (Q+s)^2 + Q^2 ; rewrite (Q+s)->P.
     case le P Q : witness s with Q = P + s ; proveIdentityG: s^2 + 2*P*(P+s) =
        P^2 + (P+s)^2 ; rewrite (P+s)->Q.
   --------------------------------------------------------------------------- *)
fun sq x = mult x x;
fun dbl t = add t t;

(* oeq_rw : rewrite term `a` to `b` inside a 1-hole predicate Pabs (nat=>o ML fn
   producing the body term), given heq : oeq a b and hPa : jT (Pabs a). *)
fun oeq_rw (PabsFn, aT, bT) heq hPa =
  let
    val zF = Free("zrw", natT);
    val Pabs = Term.lambda zF (PabsFn zF);
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC aT), (("b",0), ctermC bT)] oeq_subst_vC);
  in inst OF [heq, hPa] end;

fun sqDiffPred (P,Q) =
  Abs("s", natT, oeq (add (sq (Bound 0)) (dbl (mult P Q))) (add (sq P)(sq Q)));

fun sq_diff_law (P, Q) =
  let
    val Cgoal = mkEx (sqDiffPred (P,Q))
    val tot = le_total_at (Q, P)        (* Disj (le Q P)(le P Q) ; le Q P = Ex(%p. P = Q + p) *)
    (* ---- case le Q P : P = Q + s ---- *)
    val caseA =
      let
        val leQP = le Q P
        val hAssume = Thm.assume (ctermC (jT leQP))
        val lePred = Abs("p", natT, oeq P (add Q (Bound 0)))
        val body =
          exE_elimC (lePred, Cgoal) hAssume "s_sda"
            (fn sF => fn hEq =>          (* hEq : jT (oeq P (add Q sF)) *)
               let
                 (* polynomial id in free vars sF, Q:  s^2 + 2*(Q+s)*Q = (Q+s)^2 + Q^2 *)
                 val QplusS = add Q sF
                 val idPoly = proveIdentityG
                                (add (sq sF) (dbl (mult QplusS Q)))
                                (add (sq QplusS) (sq Q))
                 (* rewrite (Q+s) -> P using hEq (oeq P (Q+s)) ; need oeq (Q+s) P = sym *)
                 val eqSym = oeqSym_g hEq    (* oeq (add Q sF) P *)
                 val rwFn = (fn z => oeq (add (sq sF) (dbl (mult z Q))) (add (sq z) (sq Q)))
                 val rewritten = oeq_rw (rwFn, QplusS, P) eqSym idPoly
                 (* rewritten : oeq (s^2 + 2*P*Q) (P^2 + Q^2) *)
               in exI_atC (sqDiffPred (P,Q)) sF rewritten end)
      in Thm.implies_intr (ctermC (jT leQP)) body end
    (* ---- case le P Q : Q = P + s ---- *)
    val caseB =
      let
        val lePQ = le P Q
        val hAssume = Thm.assume (ctermC (jT lePQ))
        val lePred = Abs("p", natT, oeq Q (add P (Bound 0)))
        val body =
          exE_elimC (lePred, Cgoal) hAssume "s_sdb"
            (fn sF => fn hEq =>          (* hEq : jT (oeq Q (add P sF)) *)
               let
                 val PplusS = add P sF
                 val idPoly = proveIdentityG
                                (add (sq sF) (dbl (mult P PplusS)))
                                (add (sq P) (sq PplusS))
                 val eqSym = oeqSym_g hEq    (* oeq (add P sF) Q *)
                 val rwFn = (fn z => oeq (add (sq sF) (dbl (mult P z))) (add (sq P) (sq z)))
                 val rewritten = oeq_rw (rwFn, PplusS, Q) eqSym idPoly
                 (* rewritten : oeq (s^2 + 2*P*Q) (P^2 + Q^2) *)
               in exI_atC (sqDiffPred (P,Q)) sF rewritten end)
      in Thm.implies_intr (ctermC (jT lePQ)) body end
  in disjE_elimC (le Q P, le P Q, mkEx (sqDiffPred (P,Q))) tot caseA caseB end;

val () = out "BRAHMA_SQDIFF_READY\n";

(* smoke: sq_diff_law on two atoms *)
val () =
  let
    val pp = Free("p_sm",natT); val qq = Free("q_sm",natT)
    val h = sq_diff_law (pp, qq)
  in out ("SMOKE sq_diff_law hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE sq_diff_law FAIL "^exnMessage e^"\n");

(* ---------------------------------------------------------------------------
   THE BRAHMAGUPTA IDENTITY.
     brahmagupta : |- Ex P. Ex Q. oeq ((a^2+b^2)*(c^2+d^2)) (add (P^2)(Q^2))
   Proof: let P0 = a*c, Q0 = b*d (the "subtracting" cross pair), Cross = a*d+b*c
   (the "adding" cross pair).  sq_diff_law (P0, Q0) gives s with
     s^2 + 2*(a*c)*(b*d) = (a*c)^2 + (b*d)^2.                            [STAR]
   The target (with witnesses s, Cross):
     (a^2+b^2)*(c^2+d^2) = s^2 + Cross^2.
   Add the common term K = 2*(a*c)*(b*d) to BOTH sides and prove the resulting
   ALL-POSITIVE identity, then cancel K (add_left_cancel):
     K + (a^2+b^2)*(c^2+d^2)
       = (a*c)^2+(b*d)^2 + (a*d+b*c)^2                  [pure poly identity #1]
       = (s^2 + K) + Cross^2                            [rewrite STAR backwards]
       = K + (s^2 + Cross^2)                            [pure poly identity #2]
   so add_left_cancel on K gives the target.  exI twice.
   --------------------------------------------------------------------------- *)
val aB = Free("a", natT);
val bB = Free("b", natT);
val cB = Free("c", natT);
val dB = Free("d", natT);

val brahmagupta =
  let
    val P0 = mult aB cB;          (* a*c *)
    val Q0 = mult bB dB;          (* b*d *)
    val Cross = add (mult aB dB) (mult bB cB);    (* a*d + b*c *)
    val lhs = mult (add (sq aB) (sq bB)) (add (sq cB) (sq dB));   (* (a^2+b^2)(c^2+d^2) *)
    val K = dbl (mult P0 Q0);                     (* 2*(a*c)*(b*d) *)

    (* sq_diff for (P0,Q0): Ex s. s^2 + 2*P0*Q0 = P0^2 + Q0^2 *)
    val sqd = sq_diff_law (P0, Q0);
    val sqdPred = sqDiffPred (P0, Q0);

    (* the existential goal we ultimately want *)
    val targetEx =
      mkEx (Abs("P", natT,
        mkEx (Abs("Q", natT,
          oeq lhs (add (sq (Bound 1)) (sq (Bound 0)))))));

    val concl =
      exE_elimC (sqdPred, targetEx) sqd "s_brh"
        (fn sF => fn hsqd =>        (* hsqd : jT (oeq (s^2 + 2*P0*Q0) (P0^2 + Q0^2)) *)
           let
             (* identity #1 : K + lhs = (P0^2 + Q0^2) + Cross^2   (all-positive) *)
             val id1 = proveIdentityG
                         (add K lhs)
                         (add (add (sq P0) (sq Q0)) (sq Cross));
             (* rewrite (P0^2+Q0^2) -> (s^2 + K) using sym hsqd inside the RHS hole *)
             val hsqdSym = oeqSym_g hsqd;     (* oeq (P0^2+Q0^2) (s^2 + K) *)
             val rwFn1 = (fn z => oeq (add K lhs) (add z (sq Cross)));
             val id1b = oeq_rw (rwFn1, add (sq P0) (sq Q0), add (sq sF) K) hsqdSym id1;
             (* id1b : oeq (K + lhs) ((s^2 + K) + Cross^2) *)
             (* identity #2 : (s^2 + K) + Cross^2 = K + (s^2 + Cross^2)  (all-positive) *)
             val id2 = proveIdentityG
                         (add (add (sq sF) K) (sq Cross))
                         (add K (add (sq sF) (sq Cross)));
             (* chain : K + lhs = K + (s^2 + Cross^2) *)
             val chained = oeqTrans_g (id1b, id2);
             (* cancel K : add_left_cancel : oeq (K+a)(K+b) ==> oeq a b *)
             val cancelled =
               let
                 val alc = beta_norm (Drule.infer_instantiate ctxtC
                       [(("m",0), ctermC K),
                        (("a",0), ctermC lhs),
                        (("b",0), ctermC (add (sq sF) (sq Cross)))] add_left_cancel_vCb);
               in alc OF [chained] end;
             (* cancelled : oeq lhs (s^2 + Cross^2) *)
             (* exI twice: introduce Q = Cross, then P = s *)
             val innerPred = Abs("Q", natT, oeq lhs (add (sq sF) (sq (Bound 0))));
             val innerEx = exI_atC innerPred Cross cancelled;   (* Ex Q. lhs = s^2 + Q^2 *)
             val outerPred = Abs("P", natT,
                 mkEx (Abs("Q", natT, oeq lhs (add (sq (Bound 1)) (sq (Bound 0))))));
           in exI_atC outerPred sF innerEx end)
  in concl end;

val () = out ("brahmagupta hyps="^Int.toString(length(Thm.hyps_of brahmagupta))^"\n");
val () = out ("brahmagupta prop = "^Syntax.string_of_term ctxtC (Thm.prop_of brahmagupta)^"\n");

(* ---- aconv against the INTENDED statement ---- *)
val brahma_intended =
  jT (mkEx (Abs("P", natT,
        mkEx (Abs("Q", natT,
          oeq (mult (add (sq aB) (sq bB)) (add (sq cB) (sq dB)))
              (add (sq (Bound 1)) (sq (Bound 0))))))));

val brahma_aconv = ((Thm.prop_of brahmagupta) aconv brahma_intended);
val brahma_0hyp  = (length (Thm.hyps_of brahmagupta) = 0);

val () = out ("brahmagupta aconv intended = "^Bool.toString brahma_aconv^"\n");
val () = out ("brahmagupta 0-hyp = "^Bool.toString brahma_0hyp^"\n");

(* ---- SOUNDNESS PROBE: the kernel must NOT have proved the FALSE
   single-square form "Ex P. lhs = P^2" (a product of two sums of two squares is
   NOT in general a perfect square, e.g. (1^2+1^2)(1^2+1^2)=4=2^2 IS, but
   (1^2+0^2)(2^2+1^2)=5 is NOT a square).  We assert that the proved prop is NOT
   aconv that bogus single-square existential. ---- *)
val brahma_probe_singlesq =
  let
    val bogus =
      jT (mkEx (Abs("P", natT,
            oeq (mult (add (sq aB) (sq bB)) (add (sq cB) (sq dB)))
                (sq (Bound 0)))));
  in not ((Thm.prop_of brahmagupta) aconv bogus) end;

(* probe 2: must not be the trivial reflexive Ex P Q. lhs = lhs (i.e. not a
   vacuous statement that ignores the P^2+Q^2 shape) — checked by aconv to the
   intended sum-of-two-squares form already (brahma_aconv), but assert the
   conclusion genuinely mentions add-of-two-squares, not a single term. *)
val brahma_probe_nontrivial = brahma_aconv;

val () =
  if brahma_probe_singlesq
  then out "PROBE_OK brahmagupta is not the false single-square form\n"
  else out "PROBE_UNSOUND brahmagupta collapsed to a single square!\n";

val () =
  if brahma_aconv andalso brahma_0hyp andalso brahma_probe_singlesq andalso brahma_probe_nontrivial
  then out "BRAHMAGUPTA_DONE\n"
  else out "BRAHMAGUPTA_FAILED\n";
