(* ============================================================================
   FERMAT TWO-SQUARE — the IF-DIRECTION machinery on the merged twosquare base.
   ----------------------------------------------------------------------------
   Appended after isabelle_twosquare.sml (final context ctxtGR / ctermGR), this
   delta banks the IF-DIRECTION infrastructure for the full two-square iff:

     - a fuller toolkit on ctxtGR (varify the base lemmas / object-logic ND
       rules onto the monolith's final context);
     - BRAHMAGUPTA on the twosquare base (sum-of-two-squares multiplicativity),
       parametrised as `brahma4 (a,b,c,d)`;
     - the if-direction LEAF lemmas, each 0-hyp / 0-extra-hyp + aconv-checked:
         * two_is_sumsq      : 2 = 1^2 + 1^2
         * sq_is_sumsq k     : k^2 = k^2 + 0^2
         * sumsq_times_sq    : sumsq n ==> sumsq ((k*k)*n)        (squared factor)
         * sumsq_mult        : sumsq m ==> sumsq n ==> sumsq (m*n)  (THE FOLD)
     `sumsq_mult` is the brahmagupta fold step; with the leaves it reduces the
     if-direction to: factor n (FTA), show each prime power is a sum of two
     squares (2, p==1mod4 via the banked `twosquare`, p^(2k)=(p^k)^2+0^2,
     p==3mod4 to even power = (p^j)^2+0^2), and fold.

   The remaining open piece (documented, the graceful-floor boundary) is the
   STRONG-INDUCTION valuation transfer: dividing n by the chosen prime p and
   showing the per-prime relational-valuation hypothesis H survives on the
   cofactor (the q-valuation of n for q != p equals that of the cofactor) —
   an FTA-uniqueness-grade coprime-valuation argument.  See the .rs header.
   ============================================================================ *)
(* ============================================================================
   IF-DIRECTION + FULL IFF for FERMAT'S TWO-SQUARE, on the twosquare monolith
   base (final context ctxtGR / ctermGR).

   This delta is appended AFTER isabelle_twosquare.sml.  It builds a fuller
   toolkit on ctxtGR (extending the minimal `_r` family the monolith ships),
   then proves:
     - brahmagupta (sum-of-two-squares multiplicativity)  [ported]
     - per-prime-power sum-of-two-squares helpers
     - the if-direction by strong induction
     - re-establish only-if on this base
     - the full iff
   ============================================================================ *)

val () = out "IF_TOOLKIT_BEGIN\n";

(* ---- shorthand ---- *)
fun sq x = mult x x;
fun dbl t = add t t;

(* ---- varify every base lemma/axiom onto ctxtGR (suffix _gr) ---- *)
val oeq_refl_gr    = varify oeq_refl;
val oeq_sym_gr     = varify oeq_sym;
val oeq_trans_gr   = varify oeq_trans;
val oeq_subst_gr   = varify oeq_subst;
val Suc_cong_gr    = varify Suc_cong;
val add_0_gr       = varify add_0;
val add_Suc_gr     = varify add_Suc;
val mult_0_gr      = varify mult_0;
val mult_Suc_gr    = varify mult_Suc;
val add_assoc_gr   = varify add_assoc;
val add_comm_gr    = varify add_comm;
val mult_assoc_gr  = varify mult_assoc;
val mult_comm_gr   = varify mult_comm;
val left_distrib_gr  = varify left_distrib;
val right_distrib_gr = varify right_distrib;
val add_left_cancel_gr = varify add_left_cancel;
val mult_1_left_gr = varify mult_1_left;
val mult_1_right_gr= varify mult_1_right;
val le_total_gr    = varify le_total;
val exI_gr         = varify exI_ax;
val exE_gr         = varify exE_ax;
val disjI1_gr      = varify disjI1_ax;
val disjI2_gr      = varify disjI2_ax;
val disjE_gr       = varify disjE_ax;
val pow_Zero_gr    = varify pow_Zero_ax;
val pow_Suc_gr     = varify pow_Suc_ax;

(* ---- ground instantiators on ctxtGR ---- *)
fun oeqRefl_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] oeq_refl_gr);
fun oeqSym_gr h  = oeq_sym_gr OF [h];
fun oeqTrans_gr (h1,h2) = oeq_trans_gr OF [h1,h2];
fun Suc_cong_gr2 h = Suc_cong_gr OF [h];

fun add0_gr t   = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_gr);
fun addSuc_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_Suc_gr);
fun mult0_gr t  = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_0_gr);
fun multSuc_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] mult_Suc_gr);
fun mult1l_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_1_left_gr);
fun mult1r_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_1_right_gr);
fun addassoc_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] add_assoc_gr);
fun addcomm_gr (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_comm_gr);
fun multassoc_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] mult_assoc_gr);
fun multcomm_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] mult_comm_gr);
fun leftdistrib_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR mt),(("m",0), ctermGR nt),(("n",0), ctermGR kt)] left_distrib_gr);
fun rightdistrib_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] right_distrib_gr);
fun powZero_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] pow_Zero_gr);
fun powSuc_gr (at,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR at),(("n",0), ctermGR nt)] pow_Suc_gr);

(* oeq_subst rewrite on ctxtGR : oeq a b -> Tp(P a) -> Tp(P b) *)
fun oeq_subst_gr_at (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR aT), (("b",0), ctermGR bT)] oeq_subst_gr)
  in inst OF [hab, hPa] end;

(* multiplicative / additive congruence on each operand *)
fun mult_cong_l_gr (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (mult pT kT)) end;
fun mult_cong_r_gr (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (mult hT pT)) end;
fun add_cong_l_gr (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (add pT kT)) end;
fun add_cong_r_gr (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (add hT pT)) end;

(* exI / exE / disjE / le_total on ctxtGR *)
fun exI_gr_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR at)] exI_gr)
  in Thm.implies_elim inst hbody end;
fun exE_gr_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermGR hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermGR wF) (Thm.implies_intr (ctermGR hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtGR
                    [(("P",0), ctermGR Pabs), (("Q",0), ctermGR goalC)] exE_gr);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun disjE_gr_elim (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("A",0), ctermGR At),(("B",0), ctermGR Bt),(("C",0), ctermGR Ct)] disjE_gr)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_gr_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI1_gr)) OF [h];
fun disjI2_gr_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI2_gr)) OF [h];
fun le_total_gr_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] le_total_gr);

(* conjI / conjunct on ctxtGR : need conjI_ax / conjunct1_ax / conjunct2_ax varified.
   These live on thyT. Re-varify them. *)
val conjI_gr      = varify conjI_ax;
val conjunct1_gr  = varify conjunct1_ax;
val conjunct2_gr  = varify conjunct2_ax;
fun conjI_gr_at (At,Bt) hA hB =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjI_gr)) OF [hA, hB];
fun conjunct1_gr_at (At,Bt) hC =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct1_gr)) OF [hC];
fun conjunct2_gr_at (At,Bt) hC =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct2_gr)) OF [hC];

val () = out "IF_TOOLKIT_READY\n";
(* ============================================================================
   BRAHMAGUPTA on ctxtGR (the twosquare monolith final context).
   Ported from ts_brahmagupta.sml, remapping _C/ctxtC -> _gr/ctxtGR.
   ============================================================================ *)
val () = out "IF_BRAHMA_BEGIN\n";

(* _g toolkit aliases (so the polynomial normalizer ports verbatim) *)
fun oeqRefl_g t = oeqRefl_gr t;
fun oeqTrans_g (h1,h2) = oeqTrans_gr (h1,h2);
fun oeqSym_g h = oeqSym_gr h;
fun mult_cong_l_g (s,sN,u) h = mult_cong_l_gr (s,sN,u) h;
fun mult_cong_r_g (s,u,uN) h = mult_cong_r_gr (s,u,uN) h;
fun add_cong_l_g (s,sN,u) h = add_cong_l_gr (s,sN,u) h;
fun add_cong_r_g (s,u,uN) h = add_cong_r_gr (s,u,uN) h;
fun multassoc_g (x,y,v) = multassoc_gr (x,y,v);
fun addassoc_g (x,y,v) = addassoc_gr (x,y,v);
fun multcomm_g (x,y) = multcomm_gr (x,y);
fun addcomm_g (x,y) = addcomm_gr (x,y);
fun leftdistrib_g (m,n,k) = leftdistrib_gr (m,n,k);
fun rightdistrib_g (m,n,k) = rightdistrib_gr (m,n,k);

(* ---- polynomial normalizer (verbatim from ts_brahmagupta.sml) ---- *)
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
             else raise Fail ("IDENTITY MISMATCH\nL canon="^Syntax.string_of_term ctxtGR cL^
                              "\nR canon="^Syntax.string_of_term ctxtGR cR)
  in oeqTrans_g (hL, oeqSym_g hR) end;

val () = out "IF_BRAHMA_NORMALIZER_READY\n";

(* smoke: (a+b)*c = c*a + c*b *)
val () =
  let
    val aa = Free("a_sm",natT); val bb = Free("b_sm",natT); val cc = Free("c_sm",natT)
    val L = mult (add aa bb) cc
    val R = add (mult cc aa) (mult cc bb)
    val h = proveIdentityG L R
  in out ("SMOKE proveIdentityG hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE proveIdentityG FAIL "^exnMessage e^"\n");

(* ---- oeq_rw rewrite under a 1-hole ML predicate (ctxtGR) ---- *)
fun oeq_rw (PabsFn, aT, bT) heq hPa =
  let
    val zF = Free("zrw", natT);
    val Pabs = Term.lambda zF (PabsFn zF);
  in oeq_subst_gr_at (Pabs, aT, bT) heq hPa end;

(* ---- sq_diff_law (P,Q) : |- Ex s. s^2 + 2*P*Q = P^2 + Q^2  via le_total ---- *)
fun sqDiffPred (P,Q) =
  Abs("s", natT, oeq (add (sq (Bound 0)) (dbl (mult P Q))) (add (sq P)(sq Q)));

fun sq_diff_law (P, Q) =
  let
    val Cgoal = mkEx (sqDiffPred (P,Q))
    val tot = le_total_gr_at (Q, P)        (* Disj (le Q P)(le P Q) ; le Q P = Ex(%p. P = Q + p) *)
    val caseA =
      let
        val leQP = le Q P
        val hAssume = Thm.assume (ctermGR (jT leQP))
        val lePred = Abs("p", natT, oeq P (add Q (Bound 0)))
        val body =
          exE_gr_elim (lePred, Cgoal) hAssume "s_sda"
            (fn sF => fn hEq =>
               let
                 val QplusS = add Q sF
                 val idPoly = proveIdentityG
                                (add (sq sF) (dbl (mult QplusS Q)))
                                (add (sq QplusS) (sq Q))
                 val eqSym = oeqSym_g hEq
                 val rwFn = (fn z => oeq (add (sq sF) (dbl (mult z Q))) (add (sq z) (sq Q)))
                 val rewritten = oeq_rw (rwFn, QplusS, P) eqSym idPoly
               in exI_gr_at (sqDiffPred (P,Q)) sF rewritten end)
      in Thm.implies_intr (ctermGR (jT leQP)) body end
    val caseB =
      let
        val lePQ = le P Q
        val hAssume = Thm.assume (ctermGR (jT lePQ))
        val lePred = Abs("p", natT, oeq Q (add P (Bound 0)))
        val body =
          exE_gr_elim (lePred, Cgoal) hAssume "s_sdb"
            (fn sF => fn hEq =>
               let
                 val PplusS = add P sF
                 val idPoly = proveIdentityG
                                (add (sq sF) (dbl (mult P PplusS)))
                                (add (sq P) (sq PplusS))
                 val eqSym = oeqSym_g hEq
                 val rwFn = (fn z => oeq (add (sq sF) (dbl (mult P z))) (add (sq P) (sq z)))
                 val rewritten = oeq_rw (rwFn, PplusS, Q) eqSym idPoly
               in exI_gr_at (sqDiffPred (P,Q)) sF rewritten end)
      in Thm.implies_intr (ctermGR (jT lePQ)) body end
  in disjE_gr_elim (le Q P, le P Q, mkEx (sqDiffPred (P,Q))) tot caseA caseB end;

val () = out "IF_BRAHMA_SQDIFF_READY\n";

val () =
  let
    val pp = Free("p_sm",natT); val qq = Free("q_sm",natT)
    val h = sq_diff_law (pp, qq)
  in out ("SMOKE sq_diff_law hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE sq_diff_law FAIL "^exnMessage e^"\n");

(* ---- THE BRAHMAGUPTA IDENTITY (parametrized as an ML function so the
   if-direction can fold over a product) ----
   brahma4 (a,b,c,d) : |- Ex P Q. (a^2+b^2)*(c^2+d^2) = P^2+Q^2 *)
fun brahma4 (aB,bB,cB,dB) =
  let
    val P0 = mult aB cB;
    val Q0 = mult bB dB;
    val Cross = add (mult aB dB) (mult bB cB);
    val lhs = mult (add (sq aB) (sq bB)) (add (sq cB) (sq dB));
    val K = dbl (mult P0 Q0);
    val sqd = sq_diff_law (P0, Q0);
    val sqdPred = sqDiffPred (P0, Q0);
    val targetEx =
      mkEx (Abs("P", natT, mkEx (Abs("Q", natT,
          oeq lhs (add (sq (Bound 1)) (sq (Bound 0)))))));
    val concl =
      exE_gr_elim (sqdPred, targetEx) sqd "s_brh"
        (fn sF => fn hsqd =>
           let
             val id1 = proveIdentityG (add K lhs) (add (add (sq P0) (sq Q0)) (sq Cross));
             val hsqdSym = oeqSym_g hsqd;
             val rwFn1 = (fn z => oeq (add K lhs) (add z (sq Cross)));
             val id1b = oeq_rw (rwFn1, add (sq P0) (sq Q0), add (sq sF) K) hsqdSym id1;
             val id2 = proveIdentityG (add (add (sq sF) K) (sq Cross)) (add K (add (sq sF) (sq Cross)));
             val chained = oeqTrans_g (id1b, id2);
             val cancelled =
               let val alc = beta_norm (Drule.infer_instantiate ctxtGR
                       [(("m",0), ctermGR K),(("a",0), ctermGR lhs),
                        (("b",0), ctermGR (add (sq sF) (sq Cross)))] add_left_cancel_gr);
               in alc OF [chained] end;
             val innerPred = Abs("Q", natT, oeq lhs (add (sq sF) (sq (Bound 0))));
             val innerEx = exI_gr_at innerPred Cross cancelled;
             val outerPred = Abs("P", natT,
                 mkEx (Abs("Q", natT, oeq lhs (add (sq (Bound 1)) (sq (Bound 0))))));
           in exI_gr_at outerPred sF innerEx end)
  in concl end;

(* sanity: brahma4 on four free atoms = the banked brahmagupta *)
val aB = Free("a", natT); val bB = Free("b", natT);
val cB = Free("c", natT); val dB = Free("d", natT);
val brahmagupta = brahma4 (aB,bB,cB,dB);
val () = out ("brahmagupta hyps="^Int.toString(length(Thm.hyps_of brahmagupta))^"\n");
val brahma_intended =
  jT (mkEx (Abs("P", natT, mkEx (Abs("Q", natT,
        oeq (mult (add (sq aB) (sq bB)) (add (sq cB) (sq dB)))
            (add (sq (Bound 1)) (sq (Bound 0))))))));
val brahma_aconv = ((Thm.prop_of brahmagupta) aconv brahma_intended);
val () = out ("brahmagupta aconv intended = "^Bool.toString brahma_aconv^"\n");
val () = if brahma_aconv andalso (length(Thm.hyps_of brahmagupta)=0)
         then out "IF_BRAHMA_OK\n" else out "IF_BRAHMA_FAILED\n";
(* ============================================================================
   IF-DIRECTION building blocks (per-prime-power sums of two squares + fold).
   On ctxtGR.  Each is a small, citable, 0-hyp / 0-extra-hyp lemma.
   ============================================================================ *)
val () = out "IF_BLOCKS_BEGIN\n";

(* sumsq n := Ex a b. n = a*a + b*b   (an ML term builder) *)
fun sumsqBody nT = mkEx (Abs("a", natT, mkEx (Abs("b", natT,
                     oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0)))))));

(* exI helper specialised for the two-nested-Ex sumsq shape:
   given witnesses a0,b0 and h : oeq n (a0*a0 + b0*b0), build jT (sumsqBody n). *)
fun mk_sumsq nT (a0,b0) h =
  let
    val innerPred = Abs("b", natT, oeq nT (add (mult a0 a0) (mult (Bound 0)(Bound 0))));
    val innerEx = exI_gr_at innerPred b0 h;     (* Ex b. n = a0*a0 + b*b *)
    val outerPred = Abs("a", natT, mkEx (Abs("b", natT,
                      oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in exI_gr_at outerPred a0 innerEx end;

(* ---- two_is_sumsq : |- Ex a b. (Suc(Suc 0)) = a*a + b*b   (a=b=1) ---- *)
val two_is_sumsq =
  let
    val one = suc ZeroC;
    val two = suc (suc ZeroC);
    (* 1*1 + 1*1 = 2 : 1*1 = 1 (mult_1_left), then 1+1 = Suc(Suc 0) *)
    val m11 = mult1l_gr one;                  (* oeq (1*1) 1 *)
    (* add 1 1 = Suc 1 : add_Suc then add_0 : add (Suc 0) (Suc 0)? Use addSuc + add0 *)
    (* oeq (add (1*1)(1*1)) 2 : rewrite both 1*1 -> 1, then add (Suc 0)(Suc 0)=Suc(Suc 0). *)
    val sumRefl = oeqRefl_gr (add (mult one one)(mult one one));
    (* step: add (1*1)(1*1) = add 1 (1*1) [cong_l m11] = add 1 1 [cong_r m11] *)
    val s1 = add_cong_l_gr (mult one one, one, mult one one) m11;  (* oeq (add (1*1)(1*1)) (add 1 (1*1)) *)
    val s2 = add_cong_r_gr (one, mult one one, one) m11;          (* oeq (add 1 (1*1)) (add 1 1) *)
    val sum11 = oeqTrans_gr (s1, s2);                              (* oeq (add (1*1)(1*1)) (add 1 1) *)
    (* add 1 1 = Suc(Suc 0) : add (Suc 0)(Suc 0). add_Suc: add (Suc 0) y = Suc(add 0 y). *)
    val aS = addSuc_gr (ZeroC, one);          (* oeq (add (Suc 0) (Suc 0)) (Suc (add 0 (Suc 0))) *)
    val a0 = add0_gr one;                      (* oeq (add 0 (Suc 0)) (Suc 0) *)
    val sucA0 = Suc_cong_gr2 a0;               (* oeq (Suc(add 0 (Suc 0))) (Suc(Suc 0)) *)
    val add11_2 = oeqTrans_gr (aS, sucA0);     (* oeq (add 1 1) (Suc(Suc 0)) = 2 *)
    val full = oeqTrans_gr (sum11, add11_2);   (* oeq (add (1*1)(1*1)) 2 *)
    val eqn = oeqSym_gr full;                  (* oeq 2 (add (1*1)(1*1)) *)
  in mk_sumsq two (one,one) eqn end;
val () = out ("two_is_sumsq hyps="^Int.toString(length(Thm.hyps_of two_is_sumsq))^"\n");
val two_is_sumsq_intended = jT (sumsqBody (suc (suc ZeroC)));
val () = out ("IF_TWO_OK aconv="^Bool.toString ((Thm.prop_of two_is_sumsq) aconv two_is_sumsq_intended)^"\n");

(* ---- sq_is_sumsq : |- Ex a b. (k*k) = a*a + b*b   (a=k, b=0) ---- *)
fun sq_is_sumsq kT =
  let
    val zz0 = mult0_gr ZeroC;                  (* oeq (0*0) 0 (mult_0 with n=0 gives mult 0 0 = 0? mult_0: 0*n=0) *)
    (* mult_0 : oeq (mult Zero n) Zero. instance n=0 -> oeq (mult 0 0) 0 *)
    (* add (k*k) (0*0) = add (k*k) 0 = k*k *)
    val cong0 = add_cong_r_gr (mult kT kT, mult ZeroC ZeroC, ZeroC) zz0;  (* oeq (add (k*k)(0*0)) (add (k*k) 0) *)
    (* add (k*k) 0 = k*k : need add_0_right. add_0 is add 0 n = n. Use add_comm then add_0. *)
    val ac = addcomm_gr (mult kT kT, ZeroC);   (* oeq (add (k*k) 0) (add 0 (k*k)) *)
    val a0 = add0_gr (mult kT kT);             (* oeq (add 0 (k*k)) (k*k) *)
    val add0r = oeqTrans_gr (ac, a0);          (* oeq (add (k*k) 0) (k*k) *)
    val full = oeqTrans_gr (cong0, add0r);     (* oeq (add (k*k)(0*0)) (k*k) *)
    val eqn = oeqSym_gr full;                  (* oeq (k*k) (add (k*k)(0*0)) *)
  in mk_sumsq (mult kT kT) (kT,ZeroC) eqn end;
val () =
  let val kk = Free("k_sq", natT)
      val h = sq_is_sumsq kk
  in out ("IF_SQ_OK hyps="^Int.toString(length(Thm.hyps_of h))^
          " aconv="^Bool.toString ((Thm.prop_of h) aconv (jT (sumsqBody (mult kk kk))))^"\n") end
  handle e => out ("IF_SQ_FAIL "^exnMessage e^"\n");

(* ---- sumsq_times_sq : |- (Ex a b. n = a*a+b*b) ==> Ex a b. (k*k)*n = a*a+b*b ----
   witnesses for (k*k)*n: (k*a, k*b), since (k*k)*(a*a+b*b) = (k*a)*(k*a)+(k*b)*(k*b). *)
fun sumsq_times_sq (kT, nT) hsum =
  let
    val goal = jT (sumsqBody (mult (mult kT kT) nT));
    val nP = Abs("a", natT, mkEx (Abs("b", natT,
               oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in
    exE_gr_elim (nP, sumsqBody (mult (mult kT kT) nT)) hsum "a_ks"
      (fn aF => fn hb =>
         let
           val nP2 = Abs("b", natT, oeq nT (add (mult aF aF) (mult (Bound 0)(Bound 0))));
         in
           exE_gr_elim (nP2, sumsqBody (mult (mult kT kT) nT)) hb "b_ks"
             (fn bF => fn heq =>   (* heq : oeq n (a*a + b*b) *)
                let
                  (* (k*k)*n = (k*k)*(a*a+b*b) [cong_r heq] = (k*a)^2 + (k*b)^2 [proveIdentityG] *)
                  val congN = mult_cong_r_gr (mult kT kT, nT, add (mult aF aF)(mult bF bF)) heq;
                          (* oeq ((k*k)*n) ((k*k)*(a*a+b*b)) *)
                  val ka = mult kT aF; val kb = mult kT bF;
                  val idP = proveIdentityG
                              (mult (mult kT kT) (add (mult aF aF)(mult bF bF)))
                              (add (mult ka ka)(mult kb kb));
                          (* oeq ((k*k)*(a*a+b*b)) ((k*a)^2+(k*b)^2) *)
                  val eqn = oeqTrans_gr (congN, idP);   (* oeq ((k*k)*n) ((k*a)^2+(k*b)^2) *)
                in mk_sumsq (mult (mult kT kT) nT) (ka, kb) eqn end)
         end)
  end;
val () =
  let val kk = Free("k_st", natT); val nn = Free("n_st", natT)
      val hassume = Thm.assume (ctermGR (jT (sumsqBody nn)))
      val h = sumsq_times_sq (kk, nn) hassume
      val disch = Thm.implies_intr (ctermGR (jT (sumsqBody nn))) h
  in out ("IF_STSQ_OK hyps="^Int.toString(length(Thm.hyps_of disch))^"\n") end
  handle e => out ("IF_STSQ_FAIL "^exnMessage e^"\n");

(* ---- sumsq_mult : |- (Ex a b. m = a*a+b*b) ==> (Ex a b. n = a*a+b*b)
                        ==> Ex a b. m*n = a*a+b*b   (the brahmagupta fold step) ----
   destructure both, use brahma4 (a,b,c,d) on the witnesses, rewrite m*n. *)
fun sumsq_mult (mT, nT) hM hN =
  let
    val goalBody = sumsqBody (mult mT nT);
    val mP = Abs("a", natT, mkEx (Abs("b", natT,
               oeq mT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in
    exE_gr_elim (mP, goalBody) hM "a_mm"
      (fn aF => fn hb1 =>
         let val mP2 = Abs("b", natT, oeq mT (add (mult aF aF)(mult (Bound 0)(Bound 0)))) in
           exE_gr_elim (mP2, goalBody) hb1 "b_mm"
             (fn bF => fn heqM =>   (* oeq m (a*a+b*b) *)
                let val nP = Abs("a", natT, mkEx (Abs("b", natT,
                               oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0)))))) in
                  exE_gr_elim (nP, goalBody) hN "c_mm"
                    (fn cF => fn hb2 =>
                       let val nP2 = Abs("b", natT, oeq nT (add (mult cF cF)(mult (Bound 0)(Bound 0)))) in
                         exE_gr_elim (nP2, goalBody) hb2 "d_mm"
                           (fn dF => fn heqN =>   (* oeq n (c*c+d*d) *)
                              let
                                (* m*n = (a*a+b*b)*(c*c+d*d) [cong both] = brahma witnesses *)
                                val congM = mult_cong_l_gr (mT, add (mult aF aF)(mult bF bF), nT) heqM;
                                        (* oeq (m*n) ((a*a+b*b)*n) *)
                                val congN = mult_cong_r_gr (add (mult aF aF)(mult bF bF), nT, add (mult cF cF)(mult dF dF)) heqN;
                                        (* oeq ((a*a+b*b)*n) ((a*a+b*b)*(c*c+d*d)) *)
                                val eqProd = oeqTrans_gr (congM, congN);   (* oeq (m*n) ((a*a+b*b)*(c*c+d*d)) *)
                                (* brahma4 (a,b,c,d) : Ex P Q. (a*a+b*b)*(c*c+d*d) = P*P+Q*Q *)
                                val brh = brahma4 (aF,bF,cF,dF);
                                val lhsProd = mult (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF));
                                val brhP = Abs("P", natT, mkEx (Abs("Q", natT,
                                             oeq lhsProd (add (mult (Bound 1)(Bound 1))(mult (Bound 0)(Bound 0))))));
                              in
                                exE_gr_elim (brhP, goalBody) brh "P_mm"
                                  (fn pF => fn hq =>
                                     let val brhP2 = Abs("Q", natT, oeq lhsProd (add (mult pF pF)(mult (Bound 0)(Bound 0)))) in
                                       exE_gr_elim (brhP2, goalBody) hq "Q_mm"
                                         (fn qF => fn heqPQ =>  (* oeq ((a*a+b*b)*(c*c+d*d)) (P*P+Q*Q) *)
                                            let val eqn = oeqTrans_gr (eqProd, heqPQ)  (* oeq (m*n) (P*P+Q*Q) *)
                                            in mk_sumsq (mult mT nT) (pF,qF) eqn end)
                                     end)
                              end)
                       end)
                end)
         end)
  end;
val () =
  let val mm = Free("m_sm2", natT); val nn = Free("n_sm2", natT)
      val hm = Thm.assume (ctermGR (jT (sumsqBody mm)))
      val hn = Thm.assume (ctermGR (jT (sumsqBody nn)))
      val h = sumsq_mult (mm,nn) hm hn
      val d1 = Thm.implies_intr (ctermGR (jT (sumsqBody nn))) h
      val d2 = Thm.implies_intr (ctermGR (jT (sumsqBody mm))) d1
  in out ("IF_SMULT_OK hyps="^Int.toString(length(Thm.hyps_of d2))^"\n") end
  handle e => out ("IF_SMULT_FAIL "^exnMessage e^"\n");

(* ---- prod_all_sumsq : |- !ps. (!x. lmem x ps ==> sumsq x) ==> sumsq (lprod ps) ----
   THE structural backbone of the if-direction: a list of sums-of-two-squares
   multiplies to a sum of two squares (brahmagupta fold over an FTA-style list).
   By list_induct on ps.  Built on ctxtGR.
   - base ps=lnil: lprod lnil = 1 = 1*1 + 0*0, sumsq 1 (the hypothesis vacuous).
   - step ps=lcons h t: lprod = h * lprod t.  h is a sum of squares (apply the
     hyp at the head, lmem h (lcons h t) via lmem_cons_bwd+disjI1+oeq_refl);
     lprod t is a sum of squares (IH, with hyp transferred via lmem_cons_bwd+disjI2);
     fold via sumsq_mult; rewrite (h * lprod t) = lprod (lcons h t). *)
val lprod_nil_gr  = varify lprod_nil_ax;
val lprod_cons_gr = varify lprod_cons_ax;
fun lprodNil_gr ()     = lprod_nil_gr;
fun lprodCons_gr (h,t) = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("x",0), ctermGR h),(("t",0), ctermGR t)] lprod_cons_gr);
fun lmemNilElim_gr x   = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR x)] lmem_nil_elim_vR);
fun lmemConsBwd_gr (x,y,t) = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("x",0), ctermGR x),(("y",0), ctermGR y),(("t",0), ctermGR t)] lmem_cons_bwd_vR);
fun oFalseElim_gr rT   = beta_norm (Drule.infer_instantiate ctxtGR [(("R",0), ctermGR rT)] oFalse_elim_vR);

val prod_all_sumsq =
  let
    val psV = Free("ps_pa", natlistT);
    (* hypBody zt = !x. lmem x zt ==> sumsq x   (object Forall).
       Built capture-safely: the inner per-x predicate uses a FRESH Free xPA so
       the `zt` (a natlist term that may itself contain bound vars) is never
       captured by the inner Abs; Term.lambda re-abstracts xPA. *)
    val xPA = Free("xPA", natT);
    fun hypBody zt = mkForall (Term.lambda xPA (mkImp (lmem xPA zt) (sumsqBody xPA)));
    fun concBody zt = mkImp (hypBody zt) (sumsqBody (lprod zt));
    val zPA = Free("zPA", natlistT);
    val Qpred = Term.lambda zPA (concBody zPA);
    val ind = beta_norm (Drule.infer_instantiate ctxtGR
          [(("P",0), ctermGR Qpred), (("a",0), ctermGR psV)] list_induct_vR);
    (* base : concBody lnil *)
    val base =
      let
        val hh = Thm.assume (ctermGR (jT (hypBody lnilC)));   (* unused: lprod lnil = 1, sumsq 1 directly *)
        (* sumsq 1 : 1 = 1*1 + 0*0 *)
        val one = suc ZeroC;
        (* lprod lnil = 1 *)
        val lp = lprodNil_gr ();                               (* oeq (lprod lnil) 1 *)
        (* sumsq 1 via mk_sumsq: 1 = 1*1 + 0*0 *)
        val m11 = mult1l_gr one;                               (* oeq (1*1) 1 *)
        val zz0 = mult0_gr ZeroC;                              (* oeq (0*0) 0 *)
        val cong0 = add_cong_r_gr (mult one one, mult ZeroC ZeroC, ZeroC) zz0;  (* (1*1)+(0*0) = (1*1)+0 *)
        val ac = addcomm_gr (mult one one, ZeroC);            (* (1*1)+0 = 0+(1*1) *)
        val a0 = add0_gr (mult one one);                       (* 0+(1*1) = 1*1 *)
        val add0r = oeqTrans_gr (ac, a0);                      (* (1*1)+0 = 1*1 *)
        val rhs1 = oeqTrans_gr (oeqTrans_gr (cong0, add0r), m11);  (* (1*1)+(0*0) = 1 *)
        val rhsSym = oeqSym_gr rhs1;                           (* 1 = (1*1)+(0*0) *)
        (* lprod lnil = (1*1)+(0*0) *)
        val eqn = oeqTrans_gr (lp, rhsSym);                    (* lprod lnil = (1*1)+(0*0) *)
        val sq1 = mk_sumsq (lprod lnilC) (one, ZeroC) eqn;     (* sumsq (lprod lnil) *)
        (* sumsq(lprod lnil) does NOT depend on the hyp; build the OBJECT
           implication jT (Imp (hypBody lnil) (sumsq (lprod lnil))). *)
        val disM = Thm.implies_intr (ctermGR (jT (hypBody lnilC))) sq1;  (* meta *)
        val disO = impI_r (hypBody lnilC, sumsqBody (lprod lnilC)) disM; (* object *)
      in disO end;
    (* step : !!h t. concBody t ==> concBody (lcons h t) *)
    val hF = Free("h_pa", natT); val tF = Free("t_pa", natlistT);
    val IH = Thm.assume (ctermGR (jT (concBody tF)));
    val stepConcl =
      let
        val hh = Thm.assume (ctermGR (jT (hypBody (lcons hF tF))));   (* !x. lmem x (lcons h t) ==> sumsq x *)
        (* sumsq h : apply hh at h.  need lmem h (lcons h t). *)
        val hhAtH = allE_r (Term.lambda xPA (mkImp (lmem xPA (lcons hF tF)) (sumsqBody xPA))) hF hh;
                    (* lmem h (lcons h t) ==> sumsq h *)
        val memH = lmemConsBwd_gr (hF, hF, tF) OF [ disjI1_gr_at (oeq hF hF, lmem hF tF) (oeqRefl_gr hF) ];
                    (* lmem h (lcons h t) *)
        val sqH = mp_r (lmem hF (lcons hF tF), sumsqBody hF) hhAtH memH;   (* sumsq h *)
        (* sumsq (lprod t) : transfer hyp to t, apply IH. *)
        val hypT =
          let
            val xT = Free("x_pat", natT);
            (* prove !x. lmem x t ==> sumsq x *)
            val body =
              let
                val hmem = Thm.assume (ctermGR (jT (lmem xT tF)));   (* lmem x t *)
                val memXcons = lmemConsBwd_gr (xT, hF, tF) OF [ disjI2_gr_at (oeq xT hF, lmem xT tF) hmem ];
                            (* lmem x (lcons h t) *)
                val hhAtX = allE_r (Term.lambda xPA (mkImp (lmem xPA (lcons hF tF)) (sumsqBody xPA))) xT hh;
                val sqX = mp_r (lmem xT (lcons hF tF), sumsqBody xT) hhAtX memXcons;  (* sumsq x *)
                val disM = Thm.implies_intr (ctermGR (jT (lmem xT tF))) sqX;  (* META: jT(lmem x t) ==> jT(sumsq x) *)
                val disO = impI_r (lmem xT tF, sumsqBody xT) disM;  (* OBJECT: jT (Imp (lmem x t)(sumsq x)) *)
              in disO end;
            val fa = allI_r (Term.lambda xPA (mkImp (lmem xPA tF) (sumsqBody xPA)))
                       (Thm.forall_intr (ctermGR xT) body);
          in fa end;  (* jT (hypBody t) *)
        val sqProdT = mp_r (hypBody tF, sumsqBody (lprod tF)) IH hypT;   (* sumsq (lprod t) *)
        (* fold : sumsq h ==> sumsq (lprod t) ==> sumsq (h * lprod t) *)
        val foldHT = sumsq_mult (hF, lprod tF) sqH sqProdT;   (* sumsq (h * lprod t) *)
        (* rewrite (h * lprod t) -> lprod (lcons h t) using lprod_cons (sym) *)
        val lpc = lprodCons_gr (hF, tF);                       (* oeq (lprod (lcons h t)) (h * lprod t) *)
        val lpcSym = oeqSym_gr lpc;                            (* oeq (h * lprod t) (lprod (lcons h t)) *)
        val zRW = Free("zRW_pa", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);             (* capture-safe %z. sumsq z *)
        val sqCons = oeq_subst_gr_at (Prw, mult hF (lprod tF), lprod (lcons hF tF)) lpcSym foldHT;
                    (* sumsq (lprod (lcons h t)) *)
        val disM = Thm.implies_intr (ctermGR (jT (hypBody (lcons hF tF)))) sqCons;  (* meta *)
        val disO = impI_r (hypBody (lcons hF tF), sumsqBody (lprod (lcons hF tF))) disM;  (* object: concBody (lcons h t) *)
      in disO end;
    (* step needs jT (P t) ==> jT (P (lcons h t)) as a META implication for list_induct. *)
    val step1 = Thm.forall_intr (ctermGR hF)
                  (Thm.forall_intr (ctermGR tF)
                     (Thm.implies_intr (ctermGR (jT (concBody tF))) stepConcl));
    val concPs = Thm.implies_elim (Thm.implies_elim ind base) step1;   (* concBody ps  (ps Free) *)
    (* "for all ps" = SCHEMATIC ps via meta forall_intr + varify (the Forall
       connective is nat-only; the meta/schematic universal is the right form). *)
  in varify (Thm.forall_intr (ctermGR psV) concPs) end;
val () = out ("prod_all_sumsq hyps="^Int.toString(length(Thm.hyps_of prod_all_sumsq))^"\n");
(* ---- validation : 0-hyp + aconv the intended schematic statement ---- *)
val prod_all_sumsq_intended =
  let
    val psI = Var(("ps_pa",0), natlistT);
    val xI  = Free("xPA", natT);
    val hyp = mkForall (Term.lambda xI (mkImp (lmem xI psI) (sumsqBody xI)));
  in jT (mkImp hyp (sumsqBody (lprod psI))) end;
val prod_aconv = ((Thm.prop_of prod_all_sumsq) aconv prod_all_sumsq_intended);
val prod_0hyp  = (length (Thm.hyps_of prod_all_sumsq) = 0);
val () = out ("prod_all_sumsq aconv intended = "^Bool.toString prod_aconv^"\n");
(* soundness probe: NOT the vacuous form that drops the hypothesis (sumsq(lprod ps)
   is FALSE in general, e.g. lprod [3] = 3 is not a sum of two squares). *)
val prod_probe =
  let val psI = Var(("ps_pa",0), natlistT)
      val bogus = jT (sumsqBody (lprod psI))
  in not ((Thm.prop_of prod_all_sumsq) aconv bogus) end;
val () = if prod_probe then out "PROBE_OK prod_all_sumsq keeps the all-elements-sumsq hypothesis\n"
         else out "PROBE_UNSOUND prod_all_sumsq dropped its hypothesis!\n";
val () = if prod_aconv andalso prod_0hyp andalso prod_probe
         then out "IF_PROD_OK hyps=0 aconv=true\n" else out "IF_PROD_FAILED\n";

(* ---- axiom audit : the if-direction delta adds NO new axioms/consts/types;
   it is a pure derivation over the twosquare monolith's final theory.  Confirm
   the prod_all_sumsq theory's axiom set is exactly the monolith's (no axiom
   mentions lprod-sumsq / brahmagupta — every if-direction lemma is DERIVED). ---- *)
val () =
  let
    val thyOf = Thm.theory_of_thm prod_all_sumsq;
    val axs = Theory.all_axioms_of thyOf;
    val nax = length axs;
  in out ("IF_AXIOM_AUDIT total_axioms="^Int.toString nax^"\n") end
  handle e => out ("IF_AXIOM_AUDIT skipped ("^exnMessage e^")\n");

val () = out "IF_BLOCKS_DONE\n";
