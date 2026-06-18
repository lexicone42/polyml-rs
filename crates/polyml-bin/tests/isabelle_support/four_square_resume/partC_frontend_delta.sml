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
val () = out "L4_ID_PRELUDE_OK\n";
(* ============================================================================
   PART C — descent-robust seat (v2).
   ============================================================================ *)
val () = out "L4_DESCENT_SEAT_BEGIN\n";
fun sqT x = mult x x;

(* GR-level cong intro (thyGR has subv/rmodv; the base cong_introR/L use ctxtC). *)
fun cong_introR_r (m,a,b,w) hyp =   (* hyp : oeq a (add b (mult m w)) ==> cong m a b *)
  let val RAbs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val ex = exI_r RAbs w hyp
  in disjI2_r (congL m a b, congR m a b) ex end;
fun cong_introL_r (m,a,b,w) hyp =   (* hyp : oeq b (add a (mult m w)) ==> cong m a b *)
  let val LAbs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val ex = exI_r LAbs w hyp
  in disjI1_r (congL m a b, congR m a b) ex end;
val () = out "L4_CONGINTRO_R_DEFINED\n";

(* ---- pre-proved schematic identity (degree-2), proved ONCE with Frees ----
   id_sqdiff :  (d+y)*(d+y) = y*y + ((d+y)+y)*d                                 *)
val dF_id = Free("d_id", natT); val yF_id = Free("y_id", natT);
val id_sqdiff_thm =
  let val dy = add dF_id yF_id
  in proveIdentityG (mult dy dy) (add (sqT yF_id) (mult (add dy yF_id) dF_id)) end;
val id_sqdiff_v = varify id_sqdiff_thm;   (* schematic in d_id, y_id *)
val () = out ("id_sqdiff hyps="^Int.toString(length(Thm.hyps_of id_sqdiff_thm))^"\n");

(* instantiate at (d,y) — fast, no normalizer *)
fun id_sqdiff_at (dT, yT) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("d_id",0), ctermGR dT),(("y_id",0), ctermGR yT)] id_sqdiff_v);
val () = out "L4_ID_SQDIFF_DEFINED\n";

(* ----------------------------------------------------------------------------
   sqcong_of_sum (m,x,y) hxy : hxy : oeq (add x y) m  ==>  cong m (x*x)(y*y)
     case le y x : d=subv x y, d+y=x.  inst id_sqdiff at (d,y):
        (d+y)*(d+y) = y*y + ((d+y)+y)*d.  rewrite (d+y)->x (=rec0): x*x = y*y+((x)+y)*d
        rewrite (x+y)->m : x*x = y*y + m*d.  cong_introR_r.
     case le x y : d=subv y x, d+x=y.  inst id_sqdiff at (d,x):
        (d+x)*(d+x) = x*x + ((d+x)+x)*d.  rewrite (d+x)->y : y*y = x*x+((y)+x)*d
        rewrite (y+x)->m : y*y = x*x + m*d.  cong_introL_r.
   ---------------------------------------------------------------------------- *)
fun sqcong_of_sum (mT, xT, yT) hxy =
  let
    val goalC = cong mT (sqT xT) (sqT yT)
    val tot = le_total_g (yT, xT)
    val caseA =
      let
        val hP = jT (le yT xT)
        val h  = Thm.assume (ctermGR hP)
        val d  = subv xT yT
        val rec0 = sub_recover_g (xT, yT) h     (* oeq (add (subv x y) y) x : d+y=x *)
        val dy = add d yT
        val idI = id_sqdiff_at (d, yT)          (* (d+y)*(d+y) = y*y + ((d+y)+y)*d *)
        (* rewrite dy -> x in idI : predicate %z. oeq (z*z)(y*y + (z+y)*d) *)
        val zF = Free("zsc", natT)
        val Pdy = Term.lambda zF (oeq (mult zF zF) (add (sqT yT) (mult (add zF yT) d)))
        val idX = oeq_rw_r (Pdy, dy, xT) rec0 idI    (* x*x = y*y + (x+y)*d *)
        (* rewrite (x+y) -> m *)
        val zG = Free("zsc2", natT)
        val Pxy = Term.lambda zG (oeq (mult xT xT) (add (sqT yT) (mult zG d)))
        val idM = oeq_rw_r (Pxy, add xT yT, mT) hxy idX   (* x*x = y*y + m*d *)
        val cthm = cong_introR_r (mT, sqT xT, sqT yT, d) idM
      in Thm.implies_intr (ctermGR hP) cthm end
    val caseB =
      let
        val hP = jT (le xT yT)
        val h  = Thm.assume (ctermGR hP)
        val d  = subv yT xT
        val rec0 = sub_recover_g (yT, xT) h     (* d+x=y *)
        val dx = add d xT
        val idI = id_sqdiff_at (d, xT)          (* (d+x)*(d+x) = x*x + ((d+x)+x)*d *)
        val zF = Free("zsc", natT)
        val Pdx = Term.lambda zF (oeq (mult zF zF) (add (sqT xT) (mult (add zF xT) d)))
        val idY = oeq_rw_r (Pdx, dx, yT) rec0 idI    (* y*y = x*x + (y+x)*d *)
        val hyx = oeqTrans_r2 (addcomm_g (yT, xT), hxy)   (* oeq (add y x) m *)
        val zG = Free("zsc2", natT)
        val Pyx = Term.lambda zG (oeq (mult yT yT) (add (sqT xT) (mult zG d)))
        val idM = oeq_rw_r (Pyx, add yT xT, mT) hyx idY   (* y*y = x*x + m*d *)
        val cthm = cong_introL_r (mT, sqT xT, sqT yT, d) idM
      in Thm.implies_intr (ctermGR hP) cthm end
  in disjE_r (le yT xT, le xT yT, goalC) tot caseA caseB end;
val () = out "L4_SQCONG_DEFINED\n";

(* smoke *)
val () =
  let
    val mF = Free("m_sc", natT); val xF = Free("x_sc", natT); val yF = Free("y_sc", natT)
    val hxy = Thm.assume (ctermGR (jT (oeq (add xF yF) mF)))
    val r = sqcong_of_sum (mF, xF, yF) hxy
  in out ("SMOKE sqcong_of_sum : "^Syntax.string_of_term ctxtGR (Thm.prop_of r)
          ^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE sqcong_of_sum FAIL "^exnMessage e^"\n");
val () = out "L4_DESCENT_SMOKE1_OK\n";
(* ----------------------------------------------------------------------------
   le helpers (clean, no broken defs)
   ---------------------------------------------------------------------------- *)
val add_left_cancel_vGR = varify add_left_cancel;
fun alc_r (mt,at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("m",0), ctermG mt),(("a",0), ctermG at),(("b",0), ctermG bt)] add_left_cancel_vGR)) heq;

(* le_radd_cancel (x,y,z) : le (add x z)(add y z) ==> le x y *)
fun le_radd_cancel (xT, yT, zT) hle =
  let
    val goalC = le xT yT
    val Pabs = Abs("w", natT, oeq (add yT zT) (add (add xT zT) (Bound 0)))
    fun body w (hw:thm) =
      let
        val s1 = addassoc_g (xT, zT, w)
        val s2 = add_cong_r_d (xT, add zT w, add w zT) (addcomm_g (zT, w))
        val s3 = oeqSym_r2 (addassoc_g (xT, w, zT))
        val rearr = oeqTrans_r2 (oeqTrans_r2 (s1, s2), s3)   (* (x+z)+w = (x+w)+z *)
        val yz_eq = oeqTrans_r2 (hw, rearr)                  (* y+z = (x+w)+z *)
        val lc = oeqTrans_r2 (addcomm_g (yT, zT), oeqTrans_r2 (yz_eq, addcomm_g (add xT w, zT)))
        val cancel = alc_r (zT, yT, add xT w) lc             (* y = x+w *)
        val leXY = le_intro_d (xT, yT, w) cancel
      in leXY end
  in exE_r (Pabs, goalC) hle "wlrc" natT body end;
val () = out "L4_LE_RADD_CANCEL_DEFINED\n";

(* le_addsame (x,y) : le x y ==> le (add x x)(add y y) *)
fun le_addsame (xT, yT) hle =
  let
    val Pabs = Abs("w", natT, oeq yT (add xT (Bound 0)))
    val goalC = le (add xT xT)(add yT yT)
    fun body w (hw:thm) =
      let
        val yy_eq = oeqTrans_r2 (add_cong_l_d (yT, add xT w, yT) hw,
                                 add_cong_r_d (add xT w, yT, add xT w) hw)
        val idP = proveIdentityG (add (add xT w)(add xT w)) (add (add xT xT)(add w w))
        val yy_eq2 = oeqTrans_r2 (yy_eq, idP)
        val leThm = le_intro_d (add xT xT, add yT yT, add w w) yy_eq2
      in leThm end
  in exE_r (Pabs, goalC) hle "wlas" natT body end;
val () = out "L4_LE_ADDSAME_DEFINED\n";

(* lt_imp_le at GR *)
val lt_imp_le_vGR = varify lt_imp_le;
fun lt_imp_le_r (at,bt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR at),(("b",0), ctermGR bt)] lt_imp_le_vGR)) hlt;

(* le_trans at GR via _d already exists: le_trans_d *)

(* ============================================================================
   sym_residue (m, a) hm : hm : lt Zero m
        ==>  EX a'. cong m (mult a' a')(mult a a) /\ le (add a' a') m
     Construction:
       r = rmodv a m, q = rdivv a m.  a = m*q + r (divmod_id), r < m (rmod_lt).
       cong m a r  (cong_introR_r, a = r + m*q),  cong m (a*a)(r*r) (cong_sq_r).
       le_total (r+r) m:
         le (r+r) m : a':=r.  cong m (r*r)(a*a) = sym ;  le (r+r) m.
         le m (r+r) : a':=subv m r.  le r m (lt_imp_le rmod_lt).
            sub_recover: (a'+r)=m.  sqcong_of_sum (m,a',r): cong m (a'*a')(r*r).
            trans with cong m (r*r)(a*a) -> cong m (a'*a')(a*a).
            bound: le (a'+r)(r+r) [rewrite m]; le a' r [radd_cancel];
                   le (a'+a')(a'+r) [le_addsame? no: a'<=r so a'+a'<=a'+r=m].
                   actually a'+a' <= a'+r (since a'<=r, add_cong/le_add_mono) ; a'+r=m.
   ============================================================================ *)
fun sym_residue (mT, aT) hm =   (* hm : lt Zero m *)
  let
    val r = rmodv aT mT
    val q = rdivv aT mT
    val divid = divmod_id_g (aT, mT) hm     (* oeq a (add (mult m q) r) *)
    val rlt   = rmod_lt_g (aT, mT) hm       (* lt r m *)
    val rle   = lt_imp_le_r (r, mT) rlt     (* le r m *)
    (* a = r + m*q : rewrite (mult m q + r) -> (r + mult m q) *)
    val a_eq_rmq = oeqTrans_r2 (divid, addcomm_g (mult mT q, r))   (* a = r + m*q *)
    val cong_a_r = cong_introR_r (mT, aT, r, q) a_eq_rmq           (* cong m a r *)
    val cong_aa_rr = cong_sq_r (mT, aT, r) cong_a_r                (* cong m (a*a)(r*r) *)
    val goalPred = Term.lambda (Free("ap_sr", natT))
                     (mkConj (cong mT (mult (Free("ap_sr",natT))(Free("ap_sr",natT)))(mult aT aT))
                             (le (add (Free("ap_sr",natT))(Free("ap_sr",natT))) mT))
    val goalC = mkEx goalPred
    val tot = le_total_g (add r r, mT)      (* Disj (le (r+r) m)(le m (r+r)) *)
    (* CASE le (r+r) m : a':=r *)
    val caseA =
      let
        val hP = jT (le (add r r) mT)
        val h  = Thm.assume (ctermGR hP)
        val cong_rr_aa = cong_sym_g (mT, mult aT aT, mult r r) cong_aa_rr  (* cong m (r*r)(a*a) *)
        val conj = conjI_r (cong mT (mult r r)(mult aT aT), le (add r r) mT) cong_rr_aa h
        val ex = exI_r goalPred r conj
      in Thm.implies_intr (ctermGR hP) ex end
    (* CASE le m (r+r) : a':=subv m r *)
    val caseB =
      let
        val hP = jT (le mT (add r r))
        val h  = Thm.assume (ctermGR hP)
        val ap = subv mT r
        val rec0 = sub_recover_g (mT, r) rle    (* oeq (add (subv m r) r) m : a'+r=m *)
        val cong_apap_rr = sqcong_of_sum (mT, ap, r) rec0    (* cong m (a'*a')(r*r) *)
        val cong_rr_aa_B = cong_sym_g (mT, mult aT aT, mult r r) cong_aa_rr  (* cong m (r*r)(a*a) *)
        val cong_apap_aa = cong_trans_g (mT, mult ap ap, mult r r, mult aT aT) cong_apap_rr cong_rr_aa_B
        (* bound: a'+r=m <= r+r ; le (a'+r)(r+r) ; le a' r ; a'+a' <= a'+r = m *)
        val le_apr_rr = oeq_rw_r (Term.lambda (Free("zb",natT)) (le (Free("zb",natT)) (add r r)),
                                  mT, add ap r) (oeqSym_r2 rec0) h   (* le (a'+r)(r+r) *)
        val le_ap_r = le_radd_cancel (ap, r, r) le_apr_rr           (* le a' r *)
        (* le (a'+a')(a'+r) : from le a' r, add a' on left.  use le_add_mono style:
           a'+a' <= a'+r  iff  a' <= r (add a' to both).  Build via witness:
           le a' r = Ex w. r = a'+w ; then a'+r = a'+(a'+w) = (a'+a')+w -> le (a'+a')(a'+r). *)
        val le_aa_ar =
          let
            val Pw = Abs("w", natT, oeq r (add ap (Bound 0)))
            fun bd w (hw:thm) =   (* hw : oeq r (add a' w) *)
              let
                (* a'+r = a'+(a'+w) = (a'+a')+w *)
                val e1 = add_cong_r_d (ap, r, add ap w) hw          (* a'+r = a'+(a'+w) *)
                val e2 = oeqSym_r2 (addassoc_g (ap, ap, w))          (* a'+(a'+w) = (a'+a')+w *)
                val ar_eq = oeqTrans_r2 (e1, e2)                     (* a'+r = (a'+a')+w *)
                val leThm = le_intro_d (add ap ap, add ap r, w) ar_eq  (* le (a'+a')(a'+r) *)
              in leThm end
          in exE_r (Pw, le (add ap ap)(add ap r)) le_ap_r "wb" natT bd end
        (* le (a'+a') m : trans le (a'+a')(a'+r) and le (a'+r) m [rewrite a'+r=m -> le=refl] *)
        val le_aa_apr_then_m = oeq_rw_r (Term.lambda (Free("zc",natT)) (le (add ap ap) (Free("zc",natT))),
                                         add ap r, mT) rec0 le_aa_ar   (* le (a'+a') m *)
        val conj = conjI_r (cong mT (mult ap ap)(mult aT aT), le (add ap ap) mT) cong_apap_aa le_aa_apr_then_m
        val ex = exI_r goalPred ap conj
      in Thm.implies_intr (ctermGR hP) ex end
  in disjE_r (le (add r r) mT, le mT (add r r), goalC) tot caseA caseB end;
val () = out "L4_SYM_RESIDUE_DEFINED\n";

(* sym_residue_thm : 0-hyp discharged lemma. *)
val sym_residue_thm =
  let
    val mF = Free("m_rs", natT); val aF = Free("a_rs", natT)
    val hmP = jT (lt ZeroC mF)
    val hm = Thm.assume (ctermGR hmP)
    val r = sym_residue (mF, aF) hm
  in Thm.implies_intr (ctermGR hmP) r end;
val () = out ("sym_residue hyps="^Int.toString(length(Thm.hyps_of sym_residue_thm))^"\n");
val () = out ("sym_residue prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of sym_residue_thm)^"\n");

val sym_residue_intended =
  let
    val mV = Free("m_rs", natT); val aV = Free("a_rs", natT)
    val apF = Free("ap_sr", natT)
    val concl = mkEx (Term.lambda apF
                  (mkConj (cong mV (mult apF apF)(mult aV aV)) (le (add apF apF) mV)))
  in Logic.mk_implies (jT (lt ZeroC mV), jT concl) end;
val sr_aconv = ((Thm.prop_of sym_residue_thm) aconv sym_residue_intended);
val sr_0hyp  = (length (Thm.hyps_of sym_residue_thm) = 0);
val () = out ("L4_RESIDUE_VALIDATE aconv="^Bool.toString sr_aconv^" zero_hyp="^Bool.toString sr_0hyp^"\n");
val () = if sr_aconv andalso sr_0hyp then out "L4_RESIDUE_OK\n" else out "L4_RESIDUE_VALIDATE_FAILED\n";
val () = out "L4_RESIDUE_SMOKE_OK\n";
(* ============================================================================
   cong_zero_imp_mult (m, X) hcong : cong m X 0 ==> EX r. oeq X (mult m r)
     congL m X 0 = Ex k. oeq 0 (add X (m*k)) -> X=0 (add_eq_zero_left) -> r:=0.
     congR m X 0 = Ex k. oeq X (add 0 (m*k)) -> X = m*k -> r:=k.
   ============================================================================ *)
fun cong_zero_imp_mult (mT, xT) hcong =
  let
    val goalP = Term.lambda (Free("rcm", natT)) (oeq xT (mult mT (Free("rcm",natT))))
    val goalC = mkEx goalP
    val Lbody = Abs("k", natT, oeq ZeroC (add xT (mult mT (Bound 0))))
    val caseL =
      let val hL = Thm.assume (ctermGR (jT (congL mT xT ZeroC)))
          fun bd k (hk:thm) =   (* hk : oeq 0 (add X (m*k)) *)
            let val hks = oeqSym_r2 hk                       (* X + m*k = 0 *)
                val xZ  = add_eq_zero_left_d (xT, mult mT k) hks  (* X = 0 *)
                (* X = m*0 : 0 = m*0 (mult0r), so X = m*0 *)
                val m0  = oeqSym_r2 (mult0r_d mT)            (* 0 = m*0 *)
                val xm0 = oeqTrans_r2 (xZ, m0)              (* X = m*0 *)
            in exI_r goalP ZeroC xm0 end
      in Thm.implies_intr (ctermGR (jT (congL mT xT ZeroC)))
           (exE_r (Lbody, goalC) hL "kLcm" natT bd) end
    val Rbody = Abs("k", natT, oeq xT (add ZeroC (mult mT (Bound 0))))
    val caseR =
      let val hR = Thm.assume (ctermGR (jT (congR mT xT ZeroC)))
          fun bd k (hk:thm) =   (* hk : oeq X (add 0 (m*k)) *)
            let val a0  = add0_d (mult mT k)                 (* 0 + m*k = m*k *)
                val xmk = oeqTrans_r2 (hk, a0)             (* X = m*k *)
            in exI_r goalP k xmk end
      in Thm.implies_intr (ctermGR (jT (congR mT xT ZeroC)))
           (exE_r (Rbody, goalC) hR "kRcm" natT bd) end
  in disjE_r (congL mT xT ZeroC, congR mT xT ZeroC, goalC) hcong caseL caseR end;
val () = out "L4_CONGZERO_MULT_DEFINED\n";

(* smoke *)
val () =
  let val mF = Free("m_cm",natT); val xF = Free("X_cm",natT)
      val hc = Thm.assume (ctermGR (jT (cong mF xF ZeroC)))
      val r = cong_zero_imp_mult (mF, xF) hc
  in out ("SMOKE cong_zero_imp_mult hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE cong_zero_imp_mult FAIL "^exnMessage e^"\n");
val () = out "L4_CONGZERO_MULT_SMOKE_OK\n";
(* ============================================================================
   four_residue_sum :
     hm   : lt Zero m
     hbody: oeq N (a*a + b*b + c*c + d*d)        [the four_sq body for N]
     hN0  : cong m N 0                            [m | N]
     ==> EX a' b' c' d' r.
            (oeq (a'*a' + b'*b' + c'*c' + d'*d') (mult m r))
          /\ le (a'+a') m /\ le (b'+b') m /\ le (c'+c') m /\ le (d'+d') m
   This sets up the SMALLER multiple m*r for the descent (r still unbounded /
   possibly 0 here; the r<m bound + r>0 exclusion are the next descent steps).
   Built by 4x sym_residue + a cong_add chain + cong_zero_imp_mult.
   ============================================================================ *)
val sym_residue_v = varify sym_residue_thm;   (* schematic in m_rs, a_rs *)
fun sym_residue_app (mT, aT) hm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("m_rs",0), ctermGR mT),(("a_rs",0), ctermGR aT)] sym_residue_v)
  in Thm.implies_elim inst hm end;   (* EX a'. cong m (a'*a')(a*a) /\ le (a'+a') m *)

fun sqT2 x = mult x x;

(* unpack one sym_residue existential; wnm = DISTINCT witness name per call. *)
fun with_residue wnm (mT, aT) hm (k : term -> thm -> thm -> thm) goalC =
  let
    val ex = sym_residue_app (mT, aT) hm
    val wF = Free(wnm, natT)
    val P = Term.lambda wF
              (mkConj (cong mT (sqT2 wF)(sqT2 aT)) (le (add wF wF) mT))
    fun bd ap (hconj:thm) =
      let val hcong = conjunct1_r (cong mT (sqT2 ap)(sqT2 aT), le (add ap ap) mT) hconj
          val hle   = conjunct2_r (cong mT (sqT2 ap)(sqT2 aT), le (add ap ap) mT) hconj
      in k ap hcong hle end
  in exE_r (P, goalC) ex wnm natT bd end;

fun four_residue_sum (mT, aT, bT, cT, dT, nT) hm hbody hN0 =
  let
    val goalP = Term.lambda (Free("a4",natT))
      (mkEx (Term.lambda (Free("b4",natT))
        (mkEx (Term.lambda (Free("c4",natT))
          (mkEx (Term.lambda (Free("d4",natT))
            (mkEx (Term.lambda (Free("r4",natT))
              (mkConj
                (oeq (add (add (sqT2 (Free("a4",natT)))(sqT2 (Free("b4",natT))))
                          (add (sqT2 (Free("c4",natT)))(sqT2 (Free("d4",natT)))))
                     (mult mT (Free("r4",natT))))
                (mkConj (le (add (Free("a4",natT))(Free("a4",natT))) mT)
                  (mkConj (le (add (Free("b4",natT))(Free("b4",natT))) mT)
                    (mkConj (le (add (Free("c4",natT))(Free("c4",natT))) mT)
                            (le (add (Free("d4",natT))(Free("d4",natT))) mT)))))))))))))
    val goalC = mkEx goalP
    fun finish a' hca hla b' hcb hlb c' hcc hlc d' hcd hld =
      let
        (* cong m (a'^2+b'^2)(a^2+b^2) *)
        val cab = cong_add_g (mT, sqT2 a', sqT2 aT, sqT2 b', sqT2 bT) hca hcb
        val ccd = cong_add_g (mT, sqT2 c', sqT2 cT, sqT2 d', sqT2 dT) hcc hcd
        (* cong m ((a'^2+b'^2)+(c'^2+d'^2))((a^2+b^2)+(c^2+d^2)) *)
        val sumLHS = add (add (sqT2 a')(sqT2 b'))(add (sqT2 c')(sqT2 d'))
        val sumRHSab = add (sqT2 aT)(sqT2 bT)
        val sumRHScd = add (sqT2 cT)(sqT2 dT)
        val csum = cong_add_g (mT, add (sqT2 a')(sqT2 b'), sumRHSab, add (sqT2 c')(sqT2 d'), sumRHScd) cab ccd
                   (* cong m sumLHS ((a^2+b^2)+(c^2+d^2)) *)
        (* (a^2+b^2)+(c^2+d^2) = N via hbody (N = ((a^2+b^2)+(c^2+d^2))) *)
        (* hbody : oeq N (add (add (a*a)(b*b))(add (c*c)(d*d))) ; sym -> RHS = N *)
        val hbodyS = oeqSym_r2 hbody    (* oeq ((a^2+b^2)+(c^2+d^2)) N *)
        val cN = oeq_rw_r (Term.lambda (Free("zfr",natT)) (cong mT sumLHS (Free("zfr",natT))),
                           add sumRHSab sumRHScd, nT) hbodyS csum   (* cong m sumLHS N *)
        val csum0 = cong_trans_g (mT, sumLHS, nT, ZeroC) cN hN0     (* cong m sumLHS 0 *)
        (* extract multiple : sumLHS = m*r *)
        val exMult = cong_zero_imp_mult (mT, sumLHS) csum0           (* EX r. sumLHS = m*r *)
        val Pr = Term.lambda (Free("rcm",natT)) (oeq sumLHS (mult mT (Free("rcm",natT))))
        fun bdr r (hr:thm) =   (* hr : oeq sumLHS (mult m r) *)
          let
            val bigConj =
              conjI_r (oeq sumLHS (mult mT r),
                       mkConj (le (add a' a') mT)(mkConj (le (add b' b') mT)(mkConj (le (add c' c') mT)(le (add d' d') mT))))
                hr
                (conjI_r (le (add a' a') mT, mkConj (le (add b' b') mT)(mkConj (le (add c' c') mT)(le (add d' d') mT)))
                   hla
                   (conjI_r (le (add b' b') mT, mkConj (le (add c' c') mT)(le (add d' d') mT))
                      hlb
                      (conjI_r (le (add c' c') mT, le (add d' d') mT) hlc hld)))
            (* nested exI: a',b',c',d',r *)
            val e1 = exI_r (Term.lambda (Free("r4",natT))
                       (mkConj (oeq sumLHS (mult mT (Free("r4",natT))))
                         (mkConj (le (add a' a') mT)(mkConj (le (add b' b') mT)(mkConj (le (add c' c') mT)(le (add d' d') mT)))))) r bigConj
            val e2 = exI_r (Term.lambda (Free("d4",natT))
                       (mkEx (Term.lambda (Free("r4",natT))
                         (mkConj (oeq (add (add (sqT2 a')(sqT2 b'))(add (sqT2 c')(sqT2 (Free("d4",natT))))) (mult mT (Free("r4",natT))))
                           (mkConj (le (add a' a') mT)(mkConj (le (add b' b') mT)(mkConj (le (add c' c') mT)(le (add (Free("d4",natT))(Free("d4",natT))) mT)))))))) d' e1
            val e3 = exI_r (Term.lambda (Free("c4",natT))
                       (mkEx (Term.lambda (Free("d4",natT))
                         (mkEx (Term.lambda (Free("r4",natT))
                           (mkConj (oeq (add (add (sqT2 a')(sqT2 b'))(add (sqT2 (Free("c4",natT)))(sqT2 (Free("d4",natT))))) (mult mT (Free("r4",natT))))
                             (mkConj (le (add a' a') mT)(mkConj (le (add b' b') mT)(mkConj (le (add (Free("c4",natT))(Free("c4",natT))) mT)(le (add (Free("d4",natT))(Free("d4",natT))) mT)))))))))) c' e2
            val e4 = exI_r (Term.lambda (Free("b4",natT))
                       (mkEx (Term.lambda (Free("c4",natT))
                         (mkEx (Term.lambda (Free("d4",natT))
                           (mkEx (Term.lambda (Free("r4",natT))
                             (mkConj (oeq (add (add (sqT2 a')(sqT2 (Free("b4",natT))))(add (sqT2 (Free("c4",natT)))(sqT2 (Free("d4",natT))))) (mult mT (Free("r4",natT))))
                               (mkConj (le (add a' a') mT)(mkConj (le (add (Free("b4",natT))(Free("b4",natT))) mT)(mkConj (le (add (Free("c4",natT))(Free("c4",natT))) mT)(le (add (Free("d4",natT))(Free("d4",natT))) mT)))))))))))) b' e3
            val e5 = exI_r goalP a' e4
          in e5 end
      in exE_r (Pr, goalC) exMult "r_frs" natT bdr end
    (* nested with_residue for a,b,c,d *)
  in
    with_residue "ares" (mT, aT) hm (fn a' => fn hca => fn hla =>
      with_residue "bres" (mT, bT) hm (fn b' => fn hcb => fn hlb =>
        with_residue "cres" (mT, cT) hm (fn c' => fn hcc => fn hlc =>
          with_residue "dres" (mT, dT) hm (fn d' => fn hcd => fn hld =>
            finish a' hca hla b' hcb hlb c' hcc hlc d' hcd hld) goalC) goalC) goalC) goalC
  end;
val () = out "L4_FOUR_RESIDUE_SUM_DEFINED\n";

(* four_residue_sum_thm : 0-hyp discharged lemma. *)
val four_residue_sum_thm =
  let
    val mF=Free("m_f",natT); val aF=Free("a_f",natT); val bF=Free("b_f",natT)
    val cF=Free("c_f",natT); val dF=Free("d_f",natT); val nF=Free("N_f",natT)
    val hmP = jT (lt ZeroC mF); val hm = Thm.assume (ctermGR hmP)
    val hbodyP = jT (oeq nF (add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF))))
    val hbody = Thm.assume (ctermGR hbodyP)
    val hN0P = jT (cong mF nF ZeroC); val hN0 = Thm.assume (ctermGR hN0P)
    val r = four_residue_sum (mF,aF,bF,cF,dF,nF) hm hbody hN0
  in Thm.implies_intr (ctermGR hmP) (Thm.implies_intr (ctermGR hbodyP) (Thm.implies_intr (ctermGR hN0P) r)) end;
val () = out ("four_residue_sum hyps="^Int.toString(length(Thm.hyps_of four_residue_sum_thm))^"\n");

(* aconv against intended statement *)
val four_residue_sum_intended =
  let
    val mF=Free("m_f",natT); val aF=Free("a_f",natT); val bF=Free("b_f",natT)
    val cF=Free("c_f",natT); val dF=Free("d_f",natT); val nF=Free("N_f",natT)
    val a4=Free("a4",natT); val b4=Free("b4",natT); val c4=Free("c4",natT)
    val d4=Free("d4",natT); val r4=Free("r4",natT)
    fun sq x = mult x x
    val bounds = mkConj (le (add a4 a4) mF)
                   (mkConj (le (add b4 b4) mF)
                     (mkConj (le (add c4 c4) mF) (le (add d4 d4) mF)))
    val sumEq  = oeq (add (add (sq a4)(sq b4))(add (sq c4)(sq d4))) (mult mF r4)
    val body   = mkConj sumEq bounds
    val exR    = mkEx (Term.lambda r4 body)
    val exD    = mkEx (Term.lambda d4 exR)
    val exC    = mkEx (Term.lambda c4 exD)
    val exB    = mkEx (Term.lambda b4 exC)
    val concl  = mkEx (Term.lambda a4 exB)
    val prem2  = oeq nF (add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF)))
  in Logic.mk_implies (jT (lt ZeroC mF),
       Logic.mk_implies (jT prem2,
         Logic.mk_implies (jT (cong mF nF ZeroC), jT concl)))
  end;
val frs_aconv = ((Thm.prop_of four_residue_sum_thm) aconv four_residue_sum_intended);
val () = out ("L4_FRS_VALIDATE aconv="^Bool.toString frs_aconv
              ^" zero_hyp="^Bool.toString (length (Thm.hyps_of four_residue_sum_thm)=0)^"\n");
val () = if frs_aconv andalso length (Thm.hyps_of four_residue_sum_thm)=0
         then out "L4_FRS_OK\n" else out "L4_FRS_VALIDATE_FAILED\n";
val () = out "L4_FOUR_RESIDUE_SUM_SMOKE_OK\n";

(* ============================================================================
   SEAT SUMMARY (honest).  PART C front-end PROVEN; descent core remains.
   ============================================================================ *)
val () = out ("L4_SEAT_RESIDUE_0HYP="^Bool.toString (length (Thm.hyps_of sym_residue_thm)=0)^"\n");
val () = out ("L4_SEAT_FRS_0HYP="^Bool.toString (length (Thm.hyps_of four_residue_sum_thm)=0)^"\n");
(* What is DONE: sym_residue (the descent's residue construction, the heart),
   cong_zero_imp_mult, four_residue_sum (the m*r decomposition setup with bounds).
   What REMAINS for the full descent step:
     (1) r=0 exclusion: a'^2+..+d'^2=0 => m|a,b,c,d => m^2 | m*p => m|p, contra prime.
     (2) r<m bound: from each 2x'<=m, 4*(a'^2+..+d'^2) <= 4m^2 => sum <= m^2 => r<=m.
     (3) Euler identity on (m*p)*(m*r)=w^2+x^2+y^2+z^2 (proveStarFor on witnesses),
         m | w,x,y,z, divide by m^2 => r*p sum of four squares.  *)
val () = out "L4_DESCENT_PARTIAL_OK\n";
