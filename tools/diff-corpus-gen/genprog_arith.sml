(* genprog_arith.sml -- TYPE-DIRECTED program generator, ARITH_CONTROL dimension.
   ==========================================================================
   A specialization of genprog.sml focused on the ARITHMETIC + CONTROL-FLOW
   core: integer / Word / IntInf arithmetic + comparisons + boolean logic +
   let-bindings + if/then/else + case-of (on int AND bool, not just lists) +
   DEEPLY NESTED expressions. This is the "seat 0" of the genprog fan-out
   described in tools/diff-corpus-gen/genprog.sml's header; it reuses the LCG +
   typed-env + wrap + emit machinery verbatim and ADDS two numeric ty
   constructors (TyWord, TyIntInf) plus case-dispatch productions.

   WHY a SEPARATE file (vs editing the shared genprog.sml): the shared core is
   edited concurrently by the datatype/recursion/exception/gc/text seats. The
   arith_control dimension is its own batch with its own seed/prefix; keeping it
   in genprog_arith.sml means the batches never collide and each seat's edits
   stay isolated. The numeric productions here (Word, IntInf, signed div/quot/
   rem) are the genuinely NEW coverage over the int/bool/let/if already in
   genprog.sml.

   SOUNDNESS (identical to genprog.sml -- see its header):
   1. TYPE-DIRECTED => well-typed by construction => no compile errors => any @@
      divergence is a genuine OUR-vs-upstream value bug, never a test artifact.
   2. DETERMINISTIC LCG (MMIX constants) => reproducible batches.
   3. EVERY result wrapped: exn -> comparable token ("OVF"/"DIV"/...).
   4. BOUNDED depth + literal magnitudes => programs terminate fast.
   5. TOTALLY STRINGIFIED, DETERMINISTIC output:
        Int.toString / Bool.toString / Word.toString (HEX) / IntInf.toString
        (DECIMAL) / a fixed int-list/pair stringifier.
      NO Real fmt, NO ref/exn/fn PRINTING, NO andb/orb on BIG IntInf
      (the stage-0 quirk -- IntInf has NO bitwise productions here at all;
       Word DOES get bitwise, since Word is bounded and was verified identical).

   USAGE (run on the trusted UPSTREAM poly):
     GENPROG_SEED=<s> GENPROG_N=<n> GENPROG_OUT=<dir> GENPROG_PREFIX=<p> \
       /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_arith.sml
   Then:
     tools/diff-oracle.sh --dir <dir>
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir <dir>
*)

(* ===================================================================== *)
(* 0. Config (env-driven, with defaults)                                  *)
(* ===================================================================== *)
fun getInt (name, dflt) =
  case OS.Process.getEnv name of
      NONE => dflt
    | SOME s => (case Int.fromString s of SOME n => n | NONE => dflt);
fun getStr (name, dflt) =
  case OS.Process.getEnv name of NONE => dflt | SOME s => s;

val cfgSeed   = getInt ("GENPROG_SEED", 1);
val cfgN      = getInt ("GENPROG_N", 30);
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog_arith");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "ac");

(* ===================================================================== *)
(* 1. The LCG (Knuth/MMIX constants; Word is 63-bit in default-int config) *)
(* ===================================================================== *)
val s = ref (Word.fromInt cfgSeed + 0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
fun nxt () = Word.toInt (Word.>> (step (), 0w11));   (* nonnegative draw *)
fun upto n = if n <= 0 then 0 else nxt () mod n;       (* in [0,n) *)
fun bit () = upto 2;
fun chance k = upto k = 0;                             (* 1-in-k *)

(* ===================================================================== *)
(* 2. The typed environment                                               *)
(*    Closed set of types. ADDS TyWord + TyIntInf over genprog.sml.       *)
(* ===================================================================== *)
datatype ty = TyInt | TyBool | TyIntList | TyStr | TyPair | TyWord | TyIntInf;

(* the full set of types we can `let`-bind / pick a result type from *)
val allTys = [TyInt, TyBool, TyIntList, TyStr, TyPair, TyWord, TyIntInf];

type env = (string * ty) list;

val vctr = ref 0;
fun freshVar () = (vctr := !vctr + 1; "v" ^ Int.toString (!vctr));

fun varsOf (e : env, t : ty) : string list =
  List.map #1 (List.filter (fn (_, t') => t' = t) e);

fun pick xs = List.nth (xs, upto (List.length xs));

(* ===================================================================== *)
(* 3. Leaf generators (depth-0 terminals; always type-correct)            *)
(* ===================================================================== *)
fun litInt () =
  let val n = upto 21 - 10               (* -10..10 *)
  in if n < 0 then "(~" ^ Int.toString (~n) ^ ")" else Int.toString n end;

fun litBool () = if bit () = 0 then "true" else "false";

fun litIntList () =
  let val k = upto 5
      fun elems 0 = []
        | elems i = litInt () :: elems (i - 1)
  in "[" ^ String.concatWith ", " (elems k) ^ "]" end;

val alpha = "abcdefghijklmnopqrstuvwxyz0123456789 ";
fun litChar () = String.str (String.sub (alpha, upto (String.size alpha)));
fun litStr () =
  let val k = upto 6
      fun cs 0 = "" | cs i = litChar () ^ cs (i - 1)
  in "\"" ^ cs k ^ "\"" end;

fun litPair () = "(" ^ litInt () ^ ", " ^ litInt () ^ ")";

(* a Word literal. Mix small hex constants with a couple of "interesting"
   magnitudes near the tagged/word boundary. Word never overflows, so any
   constant is fine; we keep them concrete + comparable. *)
fun litWord () =
  case upto 8 of
      0 => "0w0"
    | 1 => "0w1"
    | 2 => "0w255"
    | 3 => "0wx100"
    | 4 => "(Word.fromInt " ^ litInt () ^ ")"           (* may be negative -> wraps *)
    | 5 => "0wx7FFFFFFF"
    | 6 => "0wxFFFF"
    | _ => "0w" ^ Int.toString (upto 1000);

(* an IntInf literal. Mix small ints, a near-boundary fixed value, and a
   genuine BIG bignum via IntInf.pow so the RTS arbitrary-precision path is
   exercised. Sign varied. NO bitwise here (stage-0 quirk). *)
fun litIntInf () =
  case upto 7 of
      0 => "(0 : IntInf.int)"
    | 1 => "(1 : IntInf.int)"
    | 2 => "(" ^ Int.toString (upto 1000 - 500) ^ " : IntInf.int)"
    | 3 => "(IntInf.pow (2, " ^ Int.toString (40 + upto 60) ^ "))"   (* 2^40..2^99 *)
    | 4 => "(~ (IntInf.pow (2, " ^ Int.toString (40 + upto 60) ^ ")))"
    | 5 => "(IntInf.pow (10, " ^ Int.toString (10 + upto 20) ^ "))"  (* 10^10..10^29 *)
    | _ => "(" ^ Int.toString (upto 100000) ^ " * 1000000007 : IntInf.int)";

fun leaf (e : env, t : ty) : string =
  let val vs = varsOf (e, t)
  in
    if not (List.null vs) andalso bit () = 0
    then pick vs
    else (case t of
              TyInt => litInt ()
            | TyBool => litBool ()
            | TyIntList => litIntList ()
            | TyStr => litStr ()
            | TyPair => litPair ()
            | TyWord => litWord ()
            | TyIntInf => litIntInf ())
  end;

(* ===================================================================== *)
(* 4. The type-directed core: gen (e, t, d)                                *)
(* ===================================================================== *)
fun gen (e : env, t : ty, d : int) : string =
  if d <= 0 then leaf (e, t)
  else case t of
           TyInt     => genInt (e, d)
         | TyBool    => genBool (e, d)
         | TyIntList => genList (e, d)
         | TyStr     => genStr (e, d)
         | TyPair    => genPair (e, d)
         | TyWord    => genWord (e, d)
         | TyIntInf  => genIntInf (e, d)

and genLet (e : env, t : ty, d : int) : string =
  let val bt = pick allTys
      val x = freshVar ()
      val rhs = gen (e, bt, d - 1)
      val e' = (x, bt) :: e
      val body = gen (e', t, d - 1)
  in "(let val " ^ x ^ " = " ^ rhs ^ " in " ^ body ^ " end)" end

and genIf (e : env, t : ty, d : int) : string =
  "(if " ^ gen (e, TyBool, d - 1) ^ " then " ^ gen (e, t, d - 1)
  ^ " else " ^ gen (e, t, d - 1) ^ ")"

(* ---- a CASE on an int scrutinee, arms type t. Three literal arms + a
        wildcard default => exhaustive (no Match). The scrutinee is reduced
        mod 5 so the literal arms are actually reachable, exercising real
        multi-arm dispatch (CASE / CASE16 opcode family). ---- *)
and genCaseInt (e : env, t : ty, d : int) : string =
  "(case ((" ^ gen (e, TyInt, d - 1) ^ ") mod 5) of "
  ^ "0 => " ^ gen (e, t, d - 1)
  ^ " | 1 => " ^ gen (e, t, d - 1)
  ^ " | 2 => " ^ gen (e, t, d - 1)
  ^ " | _ => " ^ gen (e, t, d - 1) ^ ")"

(* ---- a CASE on a bool scrutinee, arms type t. Exhaustive (true|false). ---- *)
and genCaseBool (e : env, t : ty, d : int) : string =
  "(case (" ^ gen (e, TyBool, d - 1) ^ ") of "
  ^ "true => " ^ gen (e, t, d - 1)
  ^ " | false => " ^ gen (e, t, d - 1) ^ ")"

and genInt (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " + " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " - " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " * " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Int.max (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(Int.min (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(~ " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Int.abs " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " div " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " mod " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Int.quot (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(Int.rem (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(List.length " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.foldl (fn (a,b) => a + b) 0 " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      (* word -> int conversions: toInt (nonneg), toIntX (signed) *)
      , fn () => "(Word.toInt (" ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.toIntX (" ^ gen (e, TyWord, d-1) ^ "))"
      (* IntInf reduced into int range so it stringifies as a small int *)
      , fn () => "(IntInf.toInt ((" ^ gen (e, TyIntInf, d-1) ^ ") mod 1000))"
      , fn () => "(IntInf.sign (" ^ gen (e, TyIntInf, d-1) ^ "))"
      (* a fuel'd recursive sum 0..n -- recursion + TCO *)
      , fn () => "(let fun f n acc = if n <= 0 then acc else f (n-1) (acc+n) in f ("
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 30) 0 end)"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      , fn () => genCaseInt (e, TyInt, d)
      , fn () => genCaseBool (e, TyInt, d)
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => 0 | x :: _ => x)"
      ]
  in (pick prods) () end

and genBool (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " < " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " <= " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " = " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " > " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " >= " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " <> " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " andalso " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " orelse " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(not " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " = " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(List.null " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStr, d-1) ^ " = " ^ gen (e, TyStr, d-1) ^ ")"
      (* Word comparisons (UNSIGNED -- semantically distinct from int <) *)
      , fn () => "(Word.< (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.<= (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.> (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "((" ^ gen (e, TyWord, d-1) ^ " : word) = " ^ gen (e, TyWord, d-1) ^ ")"
      (* IntInf comparisons (arbitrary precision) *)
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) < " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) <= " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) = " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "(List.exists (fn x => x > 0) " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.all (fn x => x < 100) " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => genIf (e, TyBool, d)
      , fn () => genLet (e, TyBool, d)
      , fn () => genCaseInt (e, TyBool, d)
      , fn () => genCaseBool (e, TyBool, d)
      ]
  in (pick prods) () end

(* ---- Word: arithmetic (wrap-on-overflow, never raises Overflow),
        bitwise (andb/orb/xorb/notb -- safe on bounded Word), and shifts
        (any amount; >= wordSize gives 0 / sign-fill, verified identical). ---- *)
and genWord (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyWord, d-1) ^ " + " ^ gen (e, TyWord, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyWord, d-1) ^ " - " ^ gen (e, TyWord, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyWord, d-1) ^ " * " ^ gen (e, TyWord, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyWord, d-1) ^ " div " ^ gen (e, TyWord, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyWord, d-1) ^ " mod " ^ gen (e, TyWord, d-1) ^ ")"
      , fn () => "(Word.andb (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.orb (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.xorb (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.notb (" ^ gen (e, TyWord, d-1) ^ "))"
      (* shifts: amount is a SMALL word so most shifts stay in-range, but a
         1-in-4 chance of a >= wordSize amount exercises the clamp path *)
      , fn () => "(Word.<< (" ^ gen (e, TyWord, d-1) ^ ", " ^ shiftAmt (e, d) ^ "))"
      , fn () => "(Word.>> (" ^ gen (e, TyWord, d-1) ^ ", " ^ shiftAmt (e, d) ^ "))"
      , fn () => "(Word.~>> (" ^ gen (e, TyWord, d-1) ^ ", " ^ shiftAmt (e, d) ^ "))"
      , fn () => "(Word.fromInt (" ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(Word.max (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(Word.min (" ^ gen (e, TyWord, d-1) ^ ", " ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => genIf (e, TyWord, d)
      , fn () => genLet (e, TyWord, d)
      , fn () => genCaseInt (e, TyWord, d)
      ]
  in (pick prods) () end

(* a shift amount: a literal word in [0,70] (so some exceed wordSize=63 and
   exercise the clamp-to-zero / sign-fill path). Kept a LITERAL so it is
   deterministic and small. *)
and shiftAmt (e, d) : string = "0w" ^ Int.toString (upto 71)

(* ---- IntInf: arbitrary-precision arithmetic. The RTS Poly*Arbitrary path
        for big operands; the boundary-crossing fixed/bignum mixes. NO
        bitwise (stage-0 quirk). div/mod/quot/rem can raise Div -> wrapped. ---- *)
and genIntInf (e, d) : string =
  let
    val prods =
      [ fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) + " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) - " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) * " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) div " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "((" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int) mod " ^ gen (e, TyIntInf, d-1) ^ ")"
      , fn () => "(IntInf.quot (" ^ gen (e, TyIntInf, d-1) ^ ", " ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(IntInf.rem (" ^ gen (e, TyIntInf, d-1) ^ ", " ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(~ (" ^ gen (e, TyIntInf, d-1) ^ " : IntInf.int))"
      , fn () => "(IntInf.abs (" ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(IntInf.max (" ^ gen (e, TyIntInf, d-1) ^ ", " ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(IntInf.min (" ^ gen (e, TyIntInf, d-1) ^ ", " ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(IntInf.fromInt (" ^ gen (e, TyInt, d-1) ^ "))"
      (* bounded pow: small exponent so the bignum stays printable + fast *)
      , fn () => "(IntInf.pow (" ^ gen (e, TyIntInf, d-1) ^ ", (Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 8)))"
      , fn () => genIf (e, TyIntInf, d)
      , fn () => genLet (e, TyIntInf, d)
      , fn () => genCaseInt (e, TyIntInf, d)
      ]
  in (pick prods) () end

and genList (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " :: " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyIntList, d-1) ^ " @ " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.rev " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.map (fn x => " ^ genIntInX (e, d-1) ^ ") " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.filter (fn x => x mod 2 = 0) " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.tabulate (Int.abs (" ^ gen (e, TyInt, d-1)
                 ^ ") mod 12, fn i => " ^ genIntInI (e, d-1) ^ "))"
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => [] | _ :: t => t)"
      , fn () => genIf (e, TyIntList, d)
      , fn () => genLet (e, TyIntList, d)
      ]
  in (pick prods) () end

and genStr (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyStr, d-1) ^ " ^ " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(Int.toString " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Bool.toString " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(Word.toString (" ^ gen (e, TyWord, d-1) ^ "))"
      , fn () => "(IntInf.toString (" ^ gen (e, TyIntInf, d-1) ^ "))"
      , fn () => "(String.substring (" ^ gen (e, TyStr, d-1)
                 ^ ", 0, 1))"
      , fn () => "(String.map Char.toUpper " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(String.concatWith \"-\" (List.map Int.toString "
                 ^ gen (e, TyIntList, d-1) ^ "))"
      , fn () => genIf (e, TyStr, d)
      , fn () => genLet (e, TyStr, d)
      ]
  in (pick prods) () end

and genPair (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(let val p = " ^ gen (e, TyPair, d-1)
                 ^ " in (#2 p, #1 p) end)"
      , fn () => genIf (e, TyPair, d)
      , fn () => genLet (e, TyPair, d)
      ]
  in (pick prods) () end

and genIntInX (e, d) : string =
  gen (("x", TyInt) :: e, TyInt, Int.max (1, d))

and genIntInI (e, d) : string =
  gen (("i", TyInt) :: e, TyInt, Int.max (1, d));

(* ===================================================================== *)
(* 5. The per-program wrapper + result stringifier                        *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog_arith.sml -- DO NOT EDIT *)\n" ^
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n";

(* the result type drives the to-string call. Word -> HEX, IntInf -> DECIMAL. *)
fun resultToString (TyInt, body)     = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)    = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body) = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)     = "wrap (fn () => (" ^ body ^ "))"
  | resultToString (TyPair, body)    = "wrap (fn () => pr2s (" ^ body ^ "))"
  | resultToString (TyWord, body)    = "wrap (fn () => Word.toString (" ^ body ^ "))"
  | resultToString (TyIntInf, body)  = "wrap (fn () => IntInf.toString (" ^ body ^ "))";

(* The arith_control dimension biases the top-level result toward the numeric
   types it is responsible for (int/word/intinf/bool); the structural types
   (list/str/pair) still appear as sub-expressions everywhere but are rarer at
   the ROOT so the batch stays focused on arithmetic + control outputs. *)
val rootTys = [TyInt, TyInt, TyBool, TyBool, TyWord, TyWord, TyIntInf, TyIntInf,
               TyIntList, TyStr, TyPair];

fun program (i : int) : string =
  let
    val () = vctr := 0
    val rt = pick rootTys
    val body = gen ([], rt, cfgDepth)
    val label = cfgPrefix ^ Int.toString i
    val rs = resultToString (rt, body)
  in
    preamble ^
    "val () = print (\"@@" ^ label ^ "=\" ^ (" ^ rs ^ ") ^ \"\\n\");\n"
  end;

(* ===================================================================== *)
(* 6. Emit N program files into cfgOut                                     *)
(* ===================================================================== *)
fun ensureDir d =
  if OS.FileSys.access (d, []) then ()
  else OS.FileSys.mkDir d;

fun writeFile (path, contents) =
  let val os = TextIO.openOut path
  in TextIO.output (os, contents); TextIO.closeOut os end;

fun emitAll () =
  let
    val () = ensureDir cfgOut
    fun loop i =
      if i >= cfgN then ()
      else
        let
          val src = program i
          val path = cfgOut ^ "/" ^ cfgPrefix ^ Int.toString i ^ ".sml"
        in
          writeFile (path, src);
          loop (i + 1)
        end
  in
    loop 0;
    print ("genprog_arith: wrote " ^ Int.toString cfgN ^ " program(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = emitAll ();
