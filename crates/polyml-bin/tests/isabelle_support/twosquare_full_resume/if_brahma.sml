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
