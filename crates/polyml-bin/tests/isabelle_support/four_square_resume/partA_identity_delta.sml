(* ============================================================================
   PART A : EULER FOUR-SQUARE IDENTITY (multiplicativity) in N.
   Delta on /tmp/l4_base.sml.  Final context already ctxtGR/ctermGR on thyGR.
   Heavy polynomial reasoning on ctxtG (thyDM subset thyGR); reuse _g toolkit,
   then lift to GR for the four_sq wrapping.
   ============================================================================ *)
val () = out "L4_IDENTITY_DELTA_BEGIN\n";
(* STAR_CHEAP : when true, the assembly ASSUMES (star) instead of proving it,
   so the assembly logic can be validated in seconds.  Overridden per run. *)
val STAR_CHEAP = (case OS.Process.getEnv "L4_STAR_CHEAP" of SOME _ => true | NONE => false);

(* ----------------------------------------------------------------------------
   POLYNOMIAL NORMALIZER on ctxtG.
   canonical poly = sorted list of monomials (duplicates kept), folded right add.
   canonical monomial = sorted list of atoms, folded right mult.
   normPoly t : |- t = canon(t).  For an all-positive identity LHS=RHS, both
   sides canonicalize to the SAME term (same monomial multiset, same order), so
   the identity proof = oeqTrans(normPoly LHS, oeqSym(normPoly RHS)).
   ---------------------------------------------------------------------------- *)

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

(* ===== MONOMIALS ===== *)
fun flattenMult t =
  case destMult t of SOME(s,u) => flattenMult s @ flattenMult u | NONE => [t];

(* monoReassoc t : |- t = monOf(flattenMult t)  (right-reassociation) *)
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
                                  mult_cong_r_g (sN, u, uN) hu)   (* s*u = sN*uN *)
          fun reassocCat ([x], v) = oeqRefl_g (mult x v)
            | reassocCat (x::xs, v) =
                let val inner = reassocCat (xs, v)
                    val assoc = multassoc_g (x, monOf xs, v)
                in oeqTrans_g (assoc, mult_cong_r_g (x, mult (monOf xs) v, monOf (xs @ fu)) inner) end
            | reassocCat ([], v) = oeqRefl_g v
          val catEq = reassocCat (fs, uN)
        in oeqTrans_g (step1, catEq) end;

(* prove monOf L = monOf L' where L' is L with adjacent swap at position k.
   We bubble-sort the atom list; each adjacent swap proved by comm+assoc.
   monoSwapAdj : atom list -> index of swap (swap els i,i+1) -> |- monOf L = monOf L'. *)

(* prove: monOf (x::y::rest) = monOf (y::x::rest)  by comm at the head. *)
fun monoCommHead (x, y, rest) =
  case rest of
      [] => multcomm_g (x, y)   (* x*y = y*x *)
    | _  =>
        let val v = monOf rest
            (* x*(y*v) = (x*y)*v = (y*x)*v = y*(x*v) *)
            val a1 = oeqSym_g (multassoc_g (x, y, v))                 (* x*(y*v) = (x*y)*v *)
            val c1 = mult_cong_l_g (mult x y, mult y x, v) (multcomm_g (x,y))  (* (x*y)*v=(y*x)*v *)
            val a2 = multassoc_g (y, x, v)                            (* (y*x)*v = y*(x*v) *)
        in oeqTrans_g (oeqTrans_g (a1, c1), a2) end;

(* monoSortStep : sort one bubble pass; returns (sortedQ, |- monOf L = monOf L'')
   Simpler: recursive insertion. monoInsert x L : |- monOf (x::L) = monOf (insert x L). *)
fun monoInsert x [] = oeqRefl_g x   (* monOf [x] = x ; insert into [] is [x] *)
  | monoInsert x (y::ys) =
      if String.compare(atomKey x, atomKey y) <> GREATER
      then oeqRefl_g (monOf (x::y::ys))     (* already in place: x <= y *)
      else
        (* x > y : swap head -> y::(x::ys) then recurse into ys *)
        let
          val swap = monoCommHead (x, y, ys)            (* monOf(x::y::ys) = monOf(y::x::ys) *)
          val rec0 = monoInsert x ys                    (* monOf(x::ys) = monOf(insert x ys) *)
          val ins  = insertSorted x ys                  (* the resulting tail list *)
          (* monOf(y::x::ys) = y * monOf(x::ys) ; congr right with rec0 -> y*monOf(insert x ys) *)
          val congr =
            (case ys of
                 [] => (* monOf(y::[x]) = y*x ; rec0: monOf[x]=monOf(insert x [])= x ; trivial *)
                       oeqRefl_g (monOf (y :: x :: ys))
               | _  => mult_cong_r_g (y, monOf (x::ys), monOf ins) rec0)
        in oeqTrans_g (swap, congr) end
and insertSorted x [] = [x]
  | insertSorted x (y::ys) =
      if String.compare(atomKey x, atomKey y) <> GREATER then x::y::ys
      else y :: insertSorted x ys;

(* monoSort L : |- monOf L = monOf (sort L)  by insertion sort *)
fun sortAtoms [] = []
  | sortAtoms (x::xs) = insertSorted x (sortAtoms xs);
fun monoSort [] = raise Fail "monoSort empty"
  | monoSort [x] = oeqRefl_g x
  | monoSort (x::xs) =
      let
        val hxs = monoSort xs                       (* monOf xs = monOf(sort xs) *)
        val sx  = sortAtoms xs
        (* monOf(x::xs) = x * monOf xs = x * monOf(sort xs) = monOf(x::sort xs) *)
        val step1 = mult_cong_r_g (x, monOf xs, monOf sx) hxs   (* x*monOf xs = x*monOf(sort xs) *)
        val ins   = monoInsert x sx                 (* monOf(x::sort xs) = monOf(insert x (sort xs)) *)
      in oeqTrans_g (step1, ins) end;

(* normMono t : |- t = monOf(sort(flatten t)) *)
fun normMono t =
  let val hr = monoReassoc t                        (* t = monOf(flatten t) *)
      val fl = flattenMult t
      val hs = monoSort fl                           (* monOf(flatten t) = monOf(sort flatten t) *)
  in oeqTrans_g (hr, hs) end;

val () = out "L4_NORM_MONO_DEFINED\n";

(* smoke: (c*a)*b normalizes to a*(b*c) *)
val () =
  let
    val a = Free("a",natT); val b = Free("b",natT); val c = Free("c",natT)
    val t = mult (mult c a) b
    val h = normMono t
  in out ("SMOKE normMono : "^Syntax.string_of_term ctxtG (Thm.prop_of h)^" hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE normMono FAIL "^exnMessage e^"\n");

val () = out "L4_IDENTITY_DELTA_PHASE2_DONE\n";
(* ===== POLYNOMIALS ===== *)
(* A "poly" at the proof level is a term that is a right-folded sum of monomial
   terms.  We work with monomial-term LISTS.  monomial key = the sorted atom-name
   list joined.  We keep duplicates. *)

fun monoAtomKey m =
  String.concatWith "," (map atomKey (flattenMult m));   (* m already canonical *)

(* compare two canonical monomials by their atom-key list (length then lex) *)
fun monoCmp (m1, m2) =
  let val k1 = flattenMult m1 val k2 = flattenMult m2
      fun go ([],[]) = EQUAL | go ([],_) = LESS | go (_,[]) = GREATER
        | go (x::xs,y::ys) = (case String.compare(atomKey x, atomKey y) of EQUAL => go(xs,ys) | c => c)
  in go (k1,k2) end;

(* polyAdd: |- polyOf A = polyOf (A) trivially; we need MERGE of two sorted lists.
   mergeProof As Bs : given As,Bs are sorted canonical-monomial lists,
   |- (polyOf As) + (polyOf Bs) = polyOf (merge As Bs).
   We do it by building polyOf(As) + polyOf(Bs) and reassociating to a single
   right-folded sum of (As @ Bs), THEN sorting by adjacent swaps. *)

(* Step A: appendProof As Bs : |- polyOf As + polyOf Bs = polyOf (As @ Bs)  (reassoc). *)
fun appendProof ([a], Bs) = oeqRefl_g (add a (polyOf Bs))   (* a + polyOf Bs = polyOf(a::Bs) *)
  | appendProof (a::As, Bs) =
      let
        val rest = appendProof (As, Bs)               (* polyOf As + polyOf Bs = polyOf(As@Bs) *)
        val assoc = addassoc_g (a, polyOf As, polyOf Bs)  (* (a+polyOf As)+polyOf Bs = a+(polyOf As+polyOf Bs) *)
        val congr = add_cong_r_g (a, add (polyOf As) (polyOf Bs), polyOf (As @ Bs)) rest
      in oeqTrans_g (assoc, congr) end
  | appendProof ([], Bs) = oeqRefl_g (polyOf Bs);

(* Step B: sort a right-folded sum by insertion (analogous to monoSort but for add). *)
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

val () = out "L4_NORM_POLY_ADD_DEFINED\n";

(* smoke: (a + c) + b  ->  sort to a + (b + c) ; with monomials being single atoms *)
val () =
  let
    val a = Free("a",natT); val b = Free("b",natT); val c = Free("c",natT)
    (* build polyOf[a,c] + polyOf[b] = polyOf[a,c,b], then sort -> polyOf[a,b,c] *)
    val ap = appendProof ([a,c],[b])      (* (a+c)+b = a+(c+b) i.e. polyOf[a,c,b] *)
    val srt = polySort [a,c,b]            (* polyOf[a,c,b] = polyOf[a,b,c] *)
    val full = oeqTrans_g (ap, srt)
  in out ("SMOKE polyAdd : "^Syntax.string_of_term ctxtG (Thm.prop_of full)^" hyps="^Int.toString(length(Thm.hyps_of full))^"\n") end
  handle e => out ("SMOKE polyAdd FAIL "^exnMessage e^"\n");

val () = out "L4_IDENTITY_DELTA_PHASE3A_DONE\n";
(* ===== POLYNOMIAL MULTIPLICATION (distribution) ===== *)

(* mulMonoPoly m Bs : |- m * polyOf Bs = polyOf (map (fn n => m*n) Bs)
   left-distribute m over the right-folded sum. *)
fun mulMonoPoly m [n] = oeqRefl_g (mult m n)
  | mulMonoPoly m (n::ns) =
      let
        (* m * (n + polyOf ns) = m*n + m*polyOf ns   [leftdistrib] *)
        val ld = leftdistrib_g (m, n, polyOf ns)        (* m*(n+polyOf ns) = m*n + m*(polyOf ns) *)
        val rec0 = mulMonoPoly m ns                     (* m*polyOf ns = polyOf(map.. ns) *)
        val congr = add_cong_r_g (mult m n, mult m (polyOf ns), polyOf (map (fn x => mult m x) ns)) rec0
      in oeqTrans_g (ld, congr) end
  | mulMonoPoly _ [] = raise Fail "mulMonoPoly empty";

(* mulPolyPoly As Bs : distribute product of two polys into the flat product list *)
fun mulPolyPoly [m] Bs = mulMonoPoly m Bs
  | mulPolyPoly (m::ms) Bs =
      let
        (* (m + polyOf ms) * polyOf Bs = m*polyOf Bs + polyOf ms * polyOf Bs  [rightdistrib] *)
        val rd = rightdistrib_g (m, polyOf ms, polyOf Bs)
        val left = mulMonoPoly m Bs                      (* m*polyOf Bs = polyOf of m-times-each *)
        val rec0 = mulPolyPoly ms Bs                     (* polyOf ms*polyOf Bs = polyOf(rest) *)
        val msProd = List.concat (map (fn mm => map (fn n => mult mm n) Bs) ms)
        val mProd  = map (fn n => mult m n) Bs
        (* rd RHS = (m*polyOf Bs) + (polyOf ms*polyOf Bs)
           rewrite left summand by `left`, right summand by `rec0` *)
        val c1 = add_cong_l_g (mult m (polyOf Bs), polyOf mProd, mult (polyOf ms) (polyOf Bs)) left
                 (* m*polyOf Bs + polyOf ms*polyOf Bs = polyOf mProd + polyOf ms*polyOf Bs *)
        val c2 = add_cong_r_g (polyOf mProd, mult (polyOf ms) (polyOf Bs), polyOf msProd) rec0
                 (* polyOf mProd + polyOf ms*polyOf Bs = polyOf mProd + polyOf msProd *)
        val step = oeqTrans_g (oeqTrans_g (rd, c1), c2)
        (* now polyOf mProd + polyOf msProd = polyOf (mProd @ msProd)  [appendProof] *)
        val ap = appendProof (mProd, msProd)
      in oeqTrans_g (step, ap) end
  | mulPolyPoly [] _ = raise Fail "mulPolyPoly empty";

val () = out "L4_NORM_POLY_MUL_RAW_DEFINED\n";

(* normalize each product monomial in a list, congruence-by-congruence across the
   right-folded sum.  normMonoListEq Ms : |- polyOf Ms = polyOf (map (canon) Ms)
   where canon m = monOf(sort(flatten m)).  We rewrite each summand by normMono. *)
fun canonOf m = monOf (sortAtoms (flattenMult m));
fun normMonoListEq [m] = normMono m            (* polyOf[m] = m = canon m *)
  | normMonoListEq (m::ms) =
      let
        val hm = normMono m                    (* m = canon m *)
        val rec0 = normMonoListEq ms           (* polyOf ms = polyOf(map canon ms) *)
        val cm = canonOf m
        val c1 = add_cong_l_g (m, cm, polyOf ms) hm      (* m + polyOf ms = canon m + polyOf ms *)
        val c2 = add_cong_r_g (cm, polyOf ms, polyOf (map canonOf ms)) rec0
      in oeqTrans_g (c1, c2) end
  | normMonoListEq [] = raise Fail "normMonoListEq empty";

val () = out "L4_NORM_MONOLIST_DEFINED\n";

(* ===== FULL POLYNOMIAL NORMALIZER =====
   normPoly t : |- t = polyOf (sorted canonical monomial list of t).
   Returns also the monomial list (canonical, sorted) for inspection. *)
fun normPolyFull t =
  case destAdd t of
      SOME(s,u) =>
        let
          val (hs, Ms) = normPolyFull s        (* s = polyOf Ms (Ms sorted canonical) *)
          val (hu, Ns) = normPolyFull u        (* u = polyOf Ns *)
          (* s + u = polyOf Ms + polyOf Ns  [congr] *)
          val c1 = add_cong_l_g (s, polyOf Ms, u) hs
          val c2 = add_cong_r_g (polyOf Ms, u, polyOf Ns) hu
          val merged = oeqTrans_g (c1, c2)     (* s+u = polyOf Ms + polyOf Ns *)
          val ap = appendProof (Ms, Ns)        (* polyOf Ms + polyOf Ns = polyOf(Ms@Ns) *)
          val cat = Ms @ Ns
          val srt = polySort cat               (* polyOf(Ms@Ns) = polyOf(sort(Ms@Ns)) *)
          val sortedList = pSortList cat
          val full = oeqTrans_g (oeqTrans_g (merged, ap), srt)
        in (full, sortedList) end
    | NONE =>
        (case destMult t of
             SOME(s,u) =>
               (* could be product of polys; normalize each, distribute, normalize monos, sort *)
               let
                 val (hs, Ms) = normPolyFull s
                 val (hu, Ns) = normPolyFull u
                 val c1 = mult_cong_l_g (s, polyOf Ms, u) hs
                 val c2 = mult_cong_r_g (polyOf Ms, u, polyOf Ns) hu
                 val prodEq = oeqTrans_g (c1, c2)    (* s*u = polyOf Ms * polyOf Ns *)
                 val mul = mulPolyPoly Ms Ns         (* polyOf Ms*polyOf Ns = polyOf rawProds *)
                 val rawProds = List.concat (map (fn mm => map (fn n => mult mm n) Ns) Ms)
                 val nm = normMonoListEq rawProds    (* polyOf rawProds = polyOf(map canon rawProds) *)
                 val canonList = map canonOf rawProds
                 val srt = polySort canonList        (* = polyOf(sort canonList) *)
                 val sortedList = pSortList canonList
                 val full = oeqTrans_g (oeqTrans_g (oeqTrans_g (prodEq, mul), nm), srt)
               in (full, sortedList) end
           | NONE =>
               (* atom : a monomial of length 1; canonicalize (it's already canon) *)
               let val h = normMono t in (h, [canonOf t]) end);

val () = out "L4_NORM_POLY_FULL_DEFINED\n";

(* smoke: (a+b)*(c+d) -> a*c + a*d + b*c + b*d (sorted) *)
val () =
  let
    val a = Free("a",natT); val b = Free("b",natT); val c = Free("c",natT); val d = Free("d",natT)
    val t = mult (add a b) (add c d)
    val (h, ms) = normPolyFull t
  in out ("SMOKE normPolyFull (a+b)(c+d) : "^Syntax.string_of_term ctxtG (Thm.prop_of h)^" hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE normPolyFull FAIL "^exnMessage e^"\n");

val () = out "L4_IDENTITY_DELTA_PHASE3B_DONE\n";
(* ===== IDENTITY PROVER ===== *)
(* proveIdentityG L R : |- oeq L R   for an all-positive (no sub) polynomial
   identity.  Normalizes both sides; their canonical monomial lists must be the
   SAME term (checked) — chains L = canon, canon = R. *)
fun proveIdentityG L R =
  let
    val (hL, msL) = normPolyFull L      (* L = polyOf msL *)
    val (hR, msR) = normPolyFull R      (* R = polyOf msR *)
    val cL = polyOf msL
    val cR = polyOf msR
    val () = if (cL aconv cR) then ()
             else raise Fail ("IDENTITY MISMATCH\nL canon="^Syntax.string_of_term ctxtG cL^
                              "\nR canon="^Syntax.string_of_term ctxtG cR)
  in oeqTrans_g (hL, oeqSym_g hR) end;   (* L = canon = R *)

val () = out "L4_IDENTITY_PROVER_DEFINED\n";

(* smoke: (a+b)*(a+b) = a*a + (a*b + (a*b + b*b))  (need RHS to match canon ordering)
   Easier smoke: prove (a+b)*c = c*a + c*b  (both distribute & sort to a*c + b*c) *)
val () =
  let
    val a = Free("a",natT); val b = Free("b",natT); val c = Free("c",natT)
    val L = mult (add a b) c
    val R = add (mult c a) (mult c b)
    val h = proveIdentityG L R
  in out ("SMOKE proveIdentityG : "^Syntax.string_of_term ctxtG (Thm.prop_of h)^" hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE proveIdentityG FAIL "^exnMessage e^"\n");

val () = out "L4_IDENTITY_DELTA_PHASE4_DONE\n";
(* ============================================================================
   THE (star) ALL-POSITIVE EULER IDENTITY, as a FUNCTION of the 8 terms a..h.
     proveStarFor (a..h) : |- oeq starL starR   where
       starL = m*n + 2*(Px*Qx + Py*Qy + Pz*Qz)
       starR = w^2 + (Px^2+Qx^2) + (Py^2+Qy^2) + (Pz^2+Qz^2)
     m = a^2+b^2+c^2+d^2,  n = e^2+f^2+g^2+h^2
     w  = ae+bf+cg+dh
     Px = af+ch,  Qx = be+dg ;  Py = ag+df, Qy = bh+ce ;  Pz = ah+bg, Qz = cf+de
   Pure N polynomial identity (no subtraction) -> proveIdentityG.
   Called ONCE on the actual witnesses (avoids varifying a gigantic thm).
   ============================================================================ *)
fun sq x = mult x x;
fun dbl t = add t t;

fun proveStarFor (a,b,c,d,e,f,g,h) =
  let
    val mP = add (add (sq a) (sq b)) (add (sq c) (sq d));
    val nP = add (add (sq e) (sq f)) (add (sq g) (sq h));
    val wW  = add (add (mult a e) (mult b f)) (add (mult c g) (mult d h));
    val Px = add (mult a f) (mult c h);    val Qx = add (mult b e) (mult d g);
    val Py = add (mult a g) (mult d f);    val Qy = add (mult b h) (mult c e);
    val Pz = add (mult a h) (mult b g);    val Qz = add (mult c f) (mult d e);
    val starL =
      add (mult mP nP)
          (dbl (add (mult Px Qx) (add (mult Py Qy) (mult Pz Qz))));
    val starR =
      add (sq wW)
          (add (add (sq Px) (sq Qx))
               (add (add (sq Py) (sq Qy))
                    (add (sq Pz) (sq Qz))));
  in proveIdentityG starL starR end;

val () = out "L4_STAR_FN_DEFINED\n";

(* quick smoke (tiny: all 8 = same atom) to confirm the function builds & proves
   WITHOUT the 13-min cost.  Use a single shared atom so monomial count collapses. *)
val () =
  let
    val z = Free("z_sm", natT)
    val h = proveStarFor (z,z,z,z,z,z,z,z)
  in out ("SMOKE proveStarFor (all=z) hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE proveStarFor FAIL "^exnMessage e^"\n");

val () = out "L4_IDENTITY_DELTA_PHASE5_DONE\n";
(* ============================================================================
   sq_diff_law (P,Q) : |- EX s. oeq (add (sq s) (dbl (mult P Q))) (add (sq P)(sq Q))
   i.e. there is s = |P-Q| with  s^2 + 2*P*Q = P^2 + Q^2  (over N).
   Proof by le_total on (P,Q):
     case le Q P : s = subv P Q, add s Q = P (sub_recover).
        polynomial id (in s,Q):  s^2 + 2*(s+Q)*Q = (s+Q)^2 + Q^2,  then rewrite (s+Q)->P.
     case le P Q : s = subv Q P, add s P = Q, and 2*P*Q = 2*Q*P (comm).
   ============================================================================ *)
fun sq x = mult x x;
fun dbl t = add t t;
val add_left_cancel_vG = varify add_left_cancel;
fun add_left_cancel_g (mt,at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("m",0), ctermG mt),(("a",0), ctermG at),(("b",0), ctermG bt)] add_left_cancel_vG)) heq;

(* the existential predicate skeleton, parameterised on P,Q with bound var for s *)
fun sqDiffPred (P,Q) =
  Abs("s", natT, oeq (add (sq (Bound 0)) (dbl (mult P Q))) (add (sq P)(sq Q)));

fun sq_diff_law (P, Q) =
  let
    val tot = le_total_g (Q, P)         (* Disj (le Q P)(le P Q) *)
    val Cgoal = mkEx (sqDiffPred (P,Q))  (* the existential we want *)
    (* ---- case le Q P : s = subv P Q ---- *)
    val caseA =
      let
        val hP = jT (le Q P)
        val h  = Thm.assume (ctermG hP)
        val sT = subv P Q
        val rec0 = sub_recover_g (P, Q) h          (* oeq (add (subv P Q) Q) P *)
        (* polynomial id in free vars sT, Q:  sq sT + 2*(sT+Q)*Q = (sT+Q)^2 + Q^2  *)
        val idPoly = proveIdentityG
                       (add (sq sT) (dbl (mult (add sT Q) Q)))
                       (add (sq (add sT Q)) (sq Q))
        (* rewrite (add sT Q) -> P using rec0.  abstract z for (add sT Q). *)
        val zF = Free("zsd", natT)
        val rwPred = Term.lambda zF
                       (oeq (add (sq sT) (dbl (mult zF Q))) (add (sq zF) (sq Q)))
        (* oeq_rw_g (Pabs, a, b) hab hPa : from hab: a=b and hPa: Pabs a, get Pabs b *)
        val body = oeq_rw_g (rwPred, add sT Q, P) rec0 idPoly
                   (* : oeq (add (sq sT)(dbl(mult P Q)))(add (sq P)(sq Q)) *)
        val ex = exI_g (sqDiffPred (P,Q)) sT body
      in Thm.implies_intr (ctermG hP) ex end
    (* ---- case le P Q : s = subv Q P ---- *)
    val caseB =
      let
        val hP = jT (le P Q)
        val h  = Thm.assume (ctermG hP)
        val sT = subv Q P
        val rec0 = sub_recover_g (Q, P) h          (* oeq (add (subv Q P) P) Q *)
        (* polynomial id (vars sT,P):  sq sT + 2*P*(sT+P) = P^2 + (sT+P)^2  *)
        val idPoly = proveIdentityG
                       (add (sq sT) (dbl (mult P (add sT P))))
                       (add (sq P) (sq (add sT P)))
        val zF = Free("zsd", natT)
        val rwPred = Term.lambda zF
                       (oeq (add (sq sT) (dbl (mult P zF))) (add (sq P) (sq zF)))
        val body = oeq_rw_g (rwPred, add sT P, Q) rec0 idPoly
                   (* : oeq (add (sq sT)(dbl(mult P Q)))(add (sq P)(sq Q)) *)
        val ex = exI_g (sqDiffPred (P,Q)) sT body
      in Thm.implies_intr (ctermG hP) ex end
  in disjE_g (le Q P, le P Q, Cgoal) tot caseA caseB end;

val () = out "L4_SQDIFF_DEFINED\n";

(* smoke: sq_diff_law on two atoms p,q *)
val () =
  let
    val p = Free("p_sd",natT); val q = Free("q_sd",natT)
    val h = sq_diff_law (p, q)
  in out ("SMOKE sq_diff_law : "^Syntax.string_of_term ctxtG (Thm.prop_of h)^" hyps="^Int.toString(length(Thm.hyps_of h))^"\n") end
  handle e => out ("SMOKE sq_diff_law FAIL "^exnMessage e^"\n");

(* ---- proved ONCE on atoms, then INSTANTIATED (fast) instead of re-running the
   normalizer on degree-4 witness expansions per pair. ---- *)
val p_sda = Free("p_sda", natT);  val q_sda = Free("q_sda", natT);
val sq_diff_atoms = sq_diff_law (p_sda, q_sda);   (* EX s. oeq (s^2+2pq)(p^2+q^2) *)
val () = out ("sq_diff_atoms hyps="^Int.toString(length(Thm.hyps_of sq_diff_atoms))^"\n");
val sq_diff_atoms_v = varify sq_diff_atoms;       (* schematic ?p_sda ?q_sda *)

(* sq_diff_inst (P,Q) : EX s. oeq (s^2+2PQ)(P^2+Q^2)  (by instantiation; fast) *)
fun sq_diff_inst (P, Q) =
  beta_norm (Drule.infer_instantiate ctxtG
    [(("p_sda",0), ctermG P),(("q_sda",0), ctermG Q)] sq_diff_atoms_v);
val () = out "L4_SQDIFF_INST_DEFINED\n";

val () = out "L4_IDENTITY_DELTA_PHASE6_DONE\n";
(* ============================================================================
   PART A ASSEMBLY :  four_sq m ==> four_sq n ==> four_sq (m*n)
   Combine (star) + 3x sq_diff_law + cancellation.
   ============================================================================ *)

(* ---- ADDITIVE NORMALIZER over MARKED leaf terms (for rearranging sums whose
   leaves are opaque products / squares).  leafKey t : SOME k if t is a leaf. ---- *)
fun addLeaves leafKey t =
  case (leafKey t) of
      SOME _ => [t]
    | NONE => (case destAdd t of
                   SOME(s,u) => addLeaves leafKey s @ addLeaves leafKey u
                 | NONE => [t]);   (* treat unknown as a leaf too *)
fun leafKeyOf leafKey t =
  case leafKey t of SOME k => k | NONE => Syntax.string_of_term ctxtG t;

(* reassoc a sum-of-leaves to right-folded polyOf(addLeaves t) *)
fun addReassoc leafKey t =
  case (leafKey t) of
      SOME _ => oeqRefl_g t
    | NONE =>
       (case destAdd t of
            NONE => oeqRefl_g t
          | SOME(s,u) =>
              let
                val fs = addLeaves leafKey s
                val fu = addLeaves leafKey u
                val hs = addReassoc leafKey s
                val hu = addReassoc leafKey u
                val sN = polyOf fs val uN = polyOf fu
                val step1 = oeqTrans_g (add_cong_l_g (s, sN, u) hs,
                                        add_cong_r_g (sN, u, uN) hu)
                fun reassocCat ([x], v) = oeqRefl_g (add x v)
                  | reassocCat (x::xs, v) =
                      let val inner = reassocCat (xs, v)
                          val assoc = addassoc_g (x, polyOf xs, v)
                      in oeqTrans_g (assoc, add_cong_r_g (x, add (polyOf xs) v, polyOf (xs @ fu)) inner) end
                  | reassocCat ([], v) = oeqRefl_g v
                val catEq = reassocCat (fs, uN)
              in oeqTrans_g (step1, catEq) end);

(* insertion sort of a leaf list by leafKeyOf, with add-comm swaps *)
fun aInsert leafKey x [] = oeqRefl_g x
  | aInsert leafKey x (y::ys) =
      if String.compare(leafKeyOf leafKey x, leafKeyOf leafKey y) <> GREATER
      then oeqRefl_g (polyOf (x::y::ys))
      else
        let
          val swap = addCommHead (x, y, ys)
          val rec0 = aInsert leafKey x ys
          val ins  = aInsSorted leafKey x ys
          val congr = (case ys of [] => oeqRefl_g (polyOf (y::x::ys))
                                | _  => add_cong_r_g (y, polyOf (x::ys), polyOf ins) rec0)
        in oeqTrans_g (swap, congr) end
and aInsSorted leafKey x [] = [x]
  | aInsSorted leafKey x (y::ys) =
      if String.compare(leafKeyOf leafKey x, leafKeyOf leafKey y) <> GREATER then x::y::ys
      else y :: aInsSorted leafKey x ys;
fun aSortList leafKey [] = []
  | aSortList leafKey (x::xs) = aInsSorted leafKey x (aSortList leafKey xs);
fun aSort leafKey [] = raise Fail "aSort empty"
  | aSort leafKey [x] = oeqRefl_g x
  | aSort leafKey (x::xs) =
      let val hxs = aSort leafKey xs
          val sx  = aSortList leafKey xs
          val step1 = add_cong_r_g (x, polyOf xs, polyOf sx) hxs
          val ins   = aInsert leafKey x sx
      in oeqTrans_g (step1, ins) end;

(* additive identity over marked leaves: |- oeq L R *)
fun proveAddIdentity leafKey L R =
  let
    val hL = addReassoc leafKey L
    val fL = addLeaves leafKey L
    val sL = aSort leafKey fL
    val canL = oeqTrans_g (hL, sL)
    val hR = addReassoc leafKey R
    val fR = addLeaves leafKey R
    val sR = aSort leafKey fR
    val canR = oeqTrans_g (hR, sR)
    val cL = polyOf (aSortList leafKey fL)
    val cR = polyOf (aSortList leafKey fR)
    val () = if (cL aconv cR) then ()
             else raise Fail ("ADD-IDENTITY MISMATCH\nL="^Syntax.string_of_term ctxtG cL^
                              "\nR="^Syntax.string_of_term ctxtG cR)
  in oeqTrans_g (canL, oeqSym_g canR) end;

val () = out "L4_ADD_IDENTITY_DEFINED\n";
(* ============================================================================
   PARAMETRIC MULTIPLICATIVITY BODY.
   `star` was proved for the fixed Frees va..vh.  Generalize it (varify) so we
   can instantiate at the actual existential WITNESSES a..h.
   ============================================================================ *)

val noLeaf = (fn (_:term) => NONE);

(* term builders in 8 nat terms *)
fun mkM (a,b,c,d) = add (add (mult a a)(mult b b)) (add (mult c c)(mult d d));
fun mkW (a,b,c,d,e,f,g,h) = add (add (mult a e)(mult b f)) (add (mult c g)(mult d h));
fun mkPx (a,b,c,d,e,f,g,h) = add (mult a f)(mult c h);
fun mkQx (a,b,c,d,e,f,g,h) = add (mult b e)(mult d g);
fun mkPy (a,b,c,d,e,f,g,h) = add (mult a g)(mult d f);
fun mkQy (a,b,c,d,e,f,g,h) = add (mult b h)(mult c e);
fun mkPz (a,b,c,d,e,f,g,h) = add (mult a h)(mult b g);
fun mkQz (a,b,c,d,e,f,g,h) = add (mult c f)(mult d e);
fun sqT x = mult x x;
fun dblT t = add t t;

val add_left_cancel_vG2 = varify add_left_cancel;
fun alc_g (mt,at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("m",0), ctermG mt),(("a",0), ctermG at),(("b",0), ctermG bt)] add_left_cancel_vG2)) heq;

(* multiplicativityBody (a..h) : |- oeq (mult (mkM abcd) (mkM efgh))
                                       (fourSqBody (mult mM nM) wW sx sy sz)
   together with the witness terms (wW, sx, sy, sz). Built on ctxtG. *)
fun multiplicativityBody (a,b,c,d,e,f,g,h) =
  let
    val mM = mkM (a,b,c,d)
    val nM = mkM (e,f,g,h)
    val wW = mkW (a,b,c,d,e,f,g,h)
    val Px = mkPx (a,b,c,d,e,f,g,h)  val Qx = mkQx (a,b,c,d,e,f,g,h)
    val Py = mkPy (a,b,c,d,e,f,g,h)  val Qy = mkQy (a,b,c,d,e,f,g,h)
    val Pz = mkPz (a,b,c,d,e,f,g,h)  val Qz = mkQz (a,b,c,d,e,f,g,h)
    val mn = mult mM nM
    val XCross = add (mult Px Qx) (add (mult Py Qy) (mult Pz Qz))
    val Dcross = add XCross XCross
    val PPsum  = add (add (sqT Px)(sqT Qx)) (add (add (sqT Py)(sqT Qy)) (add (sqT Pz)(sqT Qz)))
    val starL_i = add mn Dcross
    val starR_i = add (sqT wW) PPsum
    (* prove star directly on the actual witnesses a..h (one normalizer run);
       STAR_CHEAP=true assumes it instead (1 hyp) for fast assembly validation. *)
    val star_i = if STAR_CHEAP then Thm.assume (ctermG (jT (oeq starL_i starR_i)))
                 else proveStarFor (a,b,c,d,e,f,g,h)
    (* check star_i : oeq (mn + Dcross) (wW^2 + PPsum) *)
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "STAR_I_SHAPE_OK\n"
             else (out ("STAR_I GOT  : "^Syntax.string_of_term ctxtG (Thm.prop_of star_i)^"\n");
                   out ("STAR_I WANT : "^Syntax.string_of_term ctxtG (jT (oeq starL_i starR_i))^"\n");
                   raise Fail "star_i shape")
    (* sq_diff laws by INSTANTIATION (fast); eliminate nested *)
    val lawX = sq_diff_inst (Px, Qx)
    val lawY = sq_diff_inst (Py, Qy)
    val lawZ = sq_diff_inst (Pz, Qz)
    (* the body, parameterised on witnesses, returns bodyEq : oeq mn fsShape *)
    fun assemble (sx, hx) (sy, hy) (sz, hz) =
      let
        val Lx = add (sqT sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sqT Px)(sqT Qx)
        val Ly = add (sqT sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sqT Py)(sqT Qy)
        val Lz = add (sqT sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sqT Pz)(sqT Qz)
        val sumL = add Lx (add Ly Lz)
        val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hy
        val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hz)
        val cong_x   = add_cong_l_g (Lx, Rx, add Ly Lz) hx
        val hsum = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Lz, add Ry Rz) cong_yz2)
        val SS = add (sqT sx) (add (sqT sy)(sqT sz))
        val target = add SS Dcross
        val rearr = proveAddIdentity noLeaf sumL target          (* sumL = SS+Dcross *)
        val hSS = oeqTrans_g (oeqSym_g rearr, hsum)              (* (SS+Dcross) = PPsum *)
        val starRrew = add_cong_r_g (sqT wW, PPsum, add SS Dcross) (oeqSym_g hSS)
        val chain1 = oeqTrans_g (star_i, starRrew)
        val assocBk = oeqSym_g (addassoc_g (sqT wW, SS, Dcross))
        val chain2 = oeqTrans_g (chain1, assocBk)               (* mn+Dcross = (wW^2+SS)+Dcross *)
        val wSS = add (sqT wW) SS
        val commL = addcomm_g (mn, Dcross)
        val commR = addcomm_g (wSS, Dcross)
        val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, chain2), commR)
        val canc  = alc_g (Dcross, mn, wSS) flip                (* oeq mn (wW^2+SS) *)
        val fsShape = add (add (sqT wW)(sqT sx)) (add (sqT sy)(sqT sz))
        val reshape = proveAddIdentity noLeaf wSS fsShape
        val bodyEq = oeqTrans_g (canc, reshape)                 (* oeq mn fsShape *)
      in (wW, sx, sy, sz, bodyEq) end
  in (mn, lawX, lawY, lawZ, assemble) end;

val () = out "L4_MULTBODY_DEFINED\n";
(* ============================================================================
   TOP-LEVEL THEOREM :  four_sq m ==> four_sq n ==> four_sq (mult m n)
   ============================================================================ *)

(* elim_four_sq : eliminate the 4 nested existentials of (four_sq T).
   bodyFn (a,b,c,d) (heq : oeq T (a^2+b^2+c^2+d^2)) -> proof of goalC.
   goalC must not mention a,b,c,d. *)
fun elim_four_sq pfx hFourSq T goalC bodyFn =
  let
    (* level predicates (match four_sq's exact nesting on natT) *)
    fun pA aw = mkEx (Term.lambda (Free("b_fs",natT))
                  (mkEx (Term.lambda (Free("c_fs",natT))
                    (mkEx (Term.lambda (Free("d_fs",natT))
                      (fourSqBody T aw (Free("b_fs",natT)) (Free("c_fs",natT)) (Free("d_fs",natT))))))))
    val PA = Term.lambda (Free("a_fs",natT)) (pA (Free("a_fs",natT)))
    fun pB aw bw = mkEx (Term.lambda (Free("c_fs",natT))
                    (mkEx (Term.lambda (Free("d_fs",natT))
                      (fourSqBody T aw bw (Free("c_fs",natT)) (Free("d_fs",natT))))))
    fun pC aw bw cw = mkEx (Term.lambda (Free("d_fs",natT))
                       (fourSqBody T aw bw cw (Free("d_fs",natT))))
    fun pD aw bw cw dw = fourSqBody T aw bw cw dw
  in
    exE_r (PA, goalC) hFourSq (pfx^"a_w") natT (fn aw => fn hA =>
      exE_r (Term.lambda (Free("b_fs",natT)) (pB aw (Free("b_fs",natT))), goalC) hA (pfx^"b_w") natT (fn bw => fn hB =>
        exE_r (Term.lambda (Free("c_fs",natT)) (pC aw bw (Free("c_fs",natT))), goalC) hB (pfx^"c_w") natT (fn cw => fn hC =>
          exE_r (Term.lambda (Free("d_fs",natT)) (pD aw bw cw (Free("d_fs",natT))), goalC) hC (pfx^"d_w") natT (fn dw => fn hD =>
            (* hD : oeq T (aw^2+bw^2+cw^2+dw^2) *)
            bodyFn (aw,bw,cw,dw) hD))))
  end;

val () = out "L4_ELIM_FOURSQ_DEFINED\n";

(* the multiplicativity theorem *)
val four_sq_mult =
  let
    val mF = Free("m_mul", natT); val nF = Free("n_mul", natT)
    val hmP = jT (four_sq mF); val hm = Thm.assume (ctermGR hmP)
    val hnP = jT (four_sq nF); val hn = Thm.assume (ctermGR hnP)
    val goal = four_sq (mult mF nF)   (* OBJECT-level term (exE_r wraps in Trueprop) *)
    val core =
      elim_four_sq "m" hm mF goal (fn (a,b,c,d) => fn ham =>
        elim_four_sq "n" hn nF goal (fn (e,f,g,h) => fn han =>
          let
            (* ham : oeq m (a^2+b^2+c^2+d^2) ; han : oeq n (e^2+...+h^2) *)
            val (mn, lawX, lawY, lawZ, assemble) = multiplicativityBody (a,b,c,d,e,f,g,h)
            (* mn = (mkM abcd)*(mkM efgh) *)
            (* nested exE on the 3 diff-square laws to get sx,sy,sz *)
            val sdPredX = sqDiffPred (mkPx (a,b,c,d,e,f,g,h), mkQx (a,b,c,d,e,f,g,h))
            val sdPredY = sqDiffPred (mkPy (a,b,c,d,e,f,g,h), mkQy (a,b,c,d,e,f,g,h))
            val sdPredZ = sqDiffPred (mkPz (a,b,c,d,e,f,g,h), mkQz (a,b,c,d,e,f,g,h))
            val res =
              exE_r (sdPredX, goal) lawX "sx_w" natT (fn sx => fn hx =>
                exE_r (sdPredY, goal) lawY "sy_w" natT (fn sy => fn hy =>
                  exE_r (sdPredZ, goal) lawZ "sz_w" natT (fn sz => fn hz =>
                    let
                      val (wW, sxv, syv, szv, bodyEq) = assemble (sx,hx) (sy,hy) (sz,hz)
                      (* bodyEq : oeq mn (fourSqBody mn wW sx sy sz) *)
                      (* rewrite mult m n -> mn  via ham, han *)
                      val mkMabcd = mkM (a,b,c,d)
                      val mkMefgh = mkM (e,f,g,h)
                      val e_mn1 = mult_cong_l_g (mF, mkMabcd, nF) ham   (* m*n = (mkM abcd)*n *)
                      val e_mn2 = mult_cong_r_g (mkMabcd, nF, mkMefgh) han (* (mkM abcd)*n = mn *)
                      val e_mn  = oeqTrans_g (e_mn1, e_mn2)             (* m*n = mn *)
                      (* oeq (m*n) (fourSqBody mn wW sx sy sz) *)
                      val full = oeqTrans_g (e_mn, bodyEq)
                      (* but fourSqBody's subject in bodyEq is mn, not (m*n).
                         four_sq_witness needs subject (mult m n).  Rewrite RHS subject? no:
                         bodyEq RHS = add(add(wW^2+sx^2))(sy^2+sz^2) -- subject-free.
                         full : oeq (m*n) (that RHS).  Good. *)
                      val wit = four_sq_witness (mult mF nF, wW, sxv, syv, szv) full
                    in wit end)))
          in res end))
  in Thm.implies_intr (ctermGR hmP) (Thm.implies_intr (ctermGR hnP) core) end;

val () = out ("four_sq_mult hyps="^Int.toString(length(Thm.hyps_of four_sq_mult))^"\n");
val () = out ("four_sq_mult prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of four_sq_mult)^"\n");

(* validate intended *)
val fsm_intended =
  let val mV = Free("m_mul",natT); val nV = Free("n_mul",natT)
  in Logic.mk_implies (jT (four_sq mV), Logic.mk_implies (jT (four_sq nV), jT (four_sq (mult mV nV)))) end;
val fsm_aconv = ((Thm.prop_of four_sq_mult) aconv fsm_intended);
val fsm_0hyp  = (length (Thm.hyps_of four_sq_mult) = 0);
val () = out ("L4_IDENTITY_VALIDATE aconv="^Bool.toString fsm_aconv^" zero_hyp="^Bool.toString fsm_0hyp^"\n");
val () = if fsm_aconv andalso fsm_0hyp then out "L4_IDENTITY_OK\n" else out "L4_IDENTITY_VALIDATE_FAILED\n";

(* SOUNDNESS PROBE 1: the theorem is a genuine conditional, NOT the premise-free
   conclusion (would be unsound — not every n*? is a four_sq without hyps). *)
val probe_not_unconditional =
  let val mV = Free("m_mul",natT); val nV = Free("n_mul",natT)
  in not ((Thm.prop_of four_sq_mult) aconv (jT (four_sq (mult mV nV)))) end;
val () = out ("PROBE_CONDITIONAL "^Bool.toString probe_not_unconditional^"\n");

(* SOUNDNESS PROBE 2: the conclusion is four_sq of the PRODUCT m*n, not of m+n
   or of m alone (would be the wrong theorem). *)
val probe_product =
  let val mV = Free("m_mul",natT); val nV = Free("n_mul",natT)
      val wrong = Logic.mk_implies (jT (four_sq mV),
                    Logic.mk_implies (jT (four_sq nV), jT (four_sq (add mV nV))))
  in not ((Thm.prop_of four_sq_mult) aconv wrong) end;
val () = out ("PROBE_PRODUCT "^Bool.toString probe_product^"\n");

val () = if fsm_aconv andalso fsm_0hyp andalso probe_not_unconditional andalso probe_product
         then out "L4_IDENTITY_ALL_OK\n" else out "L4_IDENTITY_PROBES_FAILED\n";
