(* genprog_strings_closures.sml -- TYPE-DIRECTED program generator, dimension
   = strings_closures.
   ==========================================================================
   Extends the shared genprog framework (tools/diff-corpus-gen/genprog.sml) for
   the strings_closures FEATURE DIMENSION:
     - strings + chars + String/Char/Substring ops (explode/implode round-trips,
       translate, tokens/fields, substring slicing/trimming, char predicates,
       Char.ord/chr boundaries, Int.fromString round-trips),
     - CLOSURES / CURRYING: partial application, functions RETURNING functions,
       captured free variables, nested lets, mutual-ish recursion via let..and.

   Same discipline as the base generator:
     - TYPE-DIRECTED => well-typed BY CONSTRUCTION (no compile errors => both
       sides compile+run identically => any @@ divergence is an OUR-side bug).
     - DETERMINISTIC LCG (MMIX constants) => reproducible batches.
     - Every result WRAPped: an exn becomes a comparable token.
     - BOUNDED depth / list / fuel => programs terminate fast.
     - TOTALLY STRINGIFIED + DETERMINISTIC output; ASCII-clean source.

   Function types are kept MONOMORPHIC (int->int, int->string, string->int,
   string->string) so the value restriction never bites and let-bound function
   values are always usable.

   USAGE (run on the trusted UPSTREAM poly):
     /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_strings_closures.sml
   Env (read via OS.Process.getEnv):
     GENPROG_SEED   (default 1)   GENPROG_N      (default 30)
     GENPROG_OUT    (default /tmp/genprog_sc)
     GENPROG_DEPTH  (default 5)   GENPROG_PREFIX (default genprog_sc_)
   Then:
     tools/diff-oracle.sh --dir <GENPROG_OUT>
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir <GENPROG_OUT>
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
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog_sc");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "genprog_sc_");

(* ===================================================================== *)
(* 1. The LCG (Knuth/MMIX constants; Word is 63-bit in default-int config) *)
(* ===================================================================== *)
val s = ref (Word.fromInt cfgSeed + 0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
fun nxt () = Word.toInt (Word.>> (step (), 0w11));
fun upto n = if n <= 0 then 0 else nxt () mod n;
fun bit () = upto 2;
fun chance k = upto k = 0;

(* ===================================================================== *)
(* 2. The typed environment                                               *)
(*    Function types are MONOMORPHIC concrete arrows.                      *)
(* ===================================================================== *)
datatype ty =
    TyInt | TyBool | TyIntList | TyStr | TyPair
  | TyChar              (* char *)
  | TyCharList          (* char list *)
  | TyStrList           (* string list *)
  | TyFnII              (* int -> int *)
  | TyFnIS              (* int -> string *)
  | TyFnSI              (* string -> int *)
  | TyFnSS;             (* string -> string *)

(* env = (name, ty) list, innermost first *)
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

(* a safe printable ASCII alphabet; no escapes, no bytes >= 0x80 *)
val alpha = "abcdefghijklmnopqrstuvwxyz0123456789 ,.-";
fun litCharRaw () = String.sub (alpha, upto (String.size alpha));
fun litChar () = "(#\"" ^ String.str (litCharRaw ()) ^ "\")";
fun litStr () =
  let val k = upto 6
      fun cs 0 = "" | cs i = String.str (litCharRaw ()) ^ cs (i - 1)
  in "\"" ^ cs k ^ "\"" end;

fun litPair () = "(" ^ litInt () ^ ", " ^ litInt () ^ ")";

fun litCharList () =
  let val k = upto 5
      fun cs 0 = [] | cs i = litChar () :: cs (i - 1)
  in "[" ^ String.concatWith ", " (cs k) ^ "]" end;

fun litStrList () =
  let val k = upto 4
      fun ss 0 = [] | ss i = litStr () :: ss (i - 1)
  in "[" ^ String.concatWith ", " (ss k) ^ "]" end;

(* function LITERAL leaves -- monomorphic; small body referencing the bound arg *)
fun litFnII () =
  let val ops = [ "(fn z => z + " ^ litInt () ^ ")"
                , "(fn z => z * " ^ litInt () ^ ")"
                , "(fn z => z - " ^ litInt () ^ ")"
                , "(fn z => Int.abs z)"
                , "(fn z => ~ z)" ]
  in pick ops end;
fun litFnIS () =
  let val ops = [ "(fn z => Int.toString z)"
                , "(fn z => Int.toString (z + " ^ litInt () ^ "))"
                , "(fn z => String.implode (List.tabulate (Int.abs z mod 5, fn _ => #\"x\")))" ]
  in pick ops end;
fun litFnSI () =
  let val ops = [ "(fn z => String.size z)"
                , "(fn z => List.length (String.explode z))"
                , "(fn z => case Int.fromString z of SOME n => n | NONE => ~1)" ]
  in pick ops end;
fun litFnSS () =
  let val ops = [ "(fn z => String.map Char.toUpper z)"
                , "(fn z => z ^ " ^ litStr () ^ ")"
                , "(fn z => String.implode (List.rev (String.explode z)))" ]
  in pick ops end;

fun leaf (e : env, t : ty) : string =
  let val vs = varsOf (e, t)
  in
    if not (List.null vs) andalso bit () = 0
    then pick vs
    else (case t of
              TyInt      => litInt ()
            | TyBool     => litBool ()
            | TyIntList  => litIntList ()
            | TyStr      => litStr ()
            | TyPair     => litPair ()
            | TyChar     => litChar ()
            | TyCharList => litCharList ()
            | TyStrList  => litStrList ()
            | TyFnII     => litFnII ()
            | TyFnIS     => litFnIS ()
            | TyFnSI     => litFnSI ()
            | TyFnSS     => litFnSS ())
  end;

(* ===================================================================== *)
(* 4. The type-directed core: gen (e, t, d)                                *)
(* ===================================================================== *)
fun gen (e : env, t : ty, d : int) : string =
  if d <= 0 then leaf (e, t)
  else case t of
           TyInt      => genInt (e, d)
         | TyBool     => genBool (e, d)
         | TyIntList  => genList (e, d)
         | TyStr      => genStr (e, d)
         | TyPair     => genPair (e, d)
         | TyChar     => genChar (e, d)
         | TyCharList => genCharList (e, d)
         | TyStrList  => genStrList (e, d)
         | TyFnII     => genFnII (e, d)
         | TyFnIS     => genFnIS (e, d)
         | TyFnSI     => genFnSI (e, d)
         | TyFnSS     => genFnSS (e, d)

(* ---- a LET that binds a fresh var of a random type, body has type t ---- *)
and genLet (e : env, t : ty, d : int) : string =
  let val bt = pick [TyInt, TyBool, TyIntList, TyStr, TyPair, TyChar,
                     TyCharList, TyStrList, TyFnII, TyFnIS, TyFnSI, TyFnSS]
      val x = freshVar ()
      val rhs = gen (e, bt, d - 1)
      val e' = (x, bt) :: e
      val body = gen (e', t, d - 1)
  in "(let val " ^ x ^ " = " ^ rhs ^ " in " ^ body ^ " end)" end

(* ---- if c then a else b, both arms type t ---- *)
and genIf (e : env, t : ty, d : int) : string =
  "(if " ^ gen (e, TyBool, d - 1) ^ " then " ^ gen (e, t, d - 1)
  ^ " else " ^ gen (e, t, d - 1) ^ ")"

and genInt (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " + " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " - " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " * " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Int.abs " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(List.length (String.explode " ^ gen (e, TyStr, d-1) ^ "))"
      , fn () => "(List.length " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(List.length " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => "(Char.ord " ^ gen (e, TyChar, d-1) ^ ")"
      (* Int.fromString round-trip: option => -1 sentinel keeps it total *)
      , fn () => "(case Int.fromString " ^ gen (e, TyStr, d-1)
                 ^ " of SOME n => n | NONE => ~1)"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      (* APPLY a generated function -- closures + currying *)
      , fn () => "(" ^ gen (e, TyFnII, d-1) ^ " " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyFnSI, d-1) ^ " " ^ gen (e, TyStr, d-1) ^ ")"
      (* APPLY-TWICE combinator: a curried function returning a function *)
      , fn () => "(let val adder = (fn a => fn b => a + b) in ((adder "
                 ^ gen (e, TyInt, d-1) ^ ") " ^ gen (e, TyInt, d-1) ^ ") end)"
      (* fuel'd recursive sum 0..n via local fun -- recursion + TCO *)
      , fn () => "(let fun f n acc = if n <= 0 then acc else f (n-1) (acc+n) in f ("
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 30) 0 end)"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => 0 | x :: _ => x)"
      ]
  in (pick prods) () end

and genBool (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " < " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " = " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " andalso " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(not " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStr, d-1) ^ " = " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStr, d-1) ^ " < " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(Char.isAlpha " ^ gen (e, TyChar, d-1) ^ ")"
      , fn () => "(Char.isDigit " ^ gen (e, TyChar, d-1) ^ ")"
      , fn () => "(Char.isSpace " ^ gen (e, TyChar, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyChar, d-1) ^ " = " ^ gen (e, TyChar, d-1) ^ ")"
      , fn () => "(String.isPrefix " ^ gen (e, TyStr, d-1) ^ " " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(String.isSubstring " ^ gen (e, TyStr, d-1) ^ " " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(List.exists Char.isUpper " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => genIf (e, TyBool, d)
      , fn () => genLet (e, TyBool, d)
      ]
  in (pick prods) () end

and genList (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " :: " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyIntList, d-1) ^ " @ " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.rev " ^ gen (e, TyIntList, d-1) ^ ")"
      (* map a GENERATED int->int closure over a list *)
      , fn () => "(List.map " ^ gen (e, TyFnII, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* char list -> int list via Char.ord (cross-domain) *)
      , fn () => "(List.map Char.ord " ^ gen (e, TyCharList, d-1) ^ ")"
      (* string list -> int list of sizes *)
      , fn () => "(List.map " ^ gen (e, TyFnSI, d-1) ^ " " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => genIf (e, TyIntList, d)
      , fn () => genLet (e, TyIntList, d)
      ]
  in (pick prods) () end

and genChar (e, d) : string =
  let
    val prods =
      [ fn () => "(Char.toUpper " ^ gen (e, TyChar, d-1) ^ ")"
      , fn () => "(Char.toLower " ^ gen (e, TyChar, d-1) ^ ")"
      (* Char.chr can raise Chr -- wrapped at the top *)
      , fn () => "(Char.chr (Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 128))"
      (* head char of a string (may raise Subscript -> wrapped) *)
      , fn () => "(String.sub (" ^ gen (e, TyStr, d-1) ^ ", 0))"
      , fn () => "(case " ^ gen (e, TyCharList, d-1)
                 ^ " of [] => #\"?\" | c :: _ => c)"
      , fn () => genIf (e, TyChar, d)
      , fn () => genLet (e, TyChar, d)
      ]
  in (pick prods) () end

and genCharList (e, d) : string =
  let
    val prods =
      [ fn () => "(String.explode " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyChar, d-1) ^ " :: " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(List.filter Char.isAlpha " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(List.map Char.toUpper " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(List.rev " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyCharList, d-1) ^ " @ " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => genIf (e, TyCharList, d)
      , fn () => genLet (e, TyCharList, d)
      ]
  in (pick prods) () end

and genStrList (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyStr, d-1) ^ " :: " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStrList, d-1) ^ " @ " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => "(List.rev " ^ gen (e, TyStrList, d-1) ^ ")"
      (* tokens / fields split a string into a string list *)
      , fn () => "(String.tokens Char.isSpace " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(String.fields (fn c => c = #\",\") " ^ gen (e, TyStr, d-1) ^ ")"
      (* map a generated string->string closure *)
      , fn () => "(List.map " ^ gen (e, TyFnSS, d-1) ^ " " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => genIf (e, TyStrList, d)
      , fn () => genLet (e, TyStrList, d)
      ]
  in (pick prods) () end

and genStr (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyStr, d-1) ^ " ^ " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(Int.toString " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Bool.toString " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(String.str " ^ gen (e, TyChar, d-1) ^ ")"
      (* implode/explode round-trip *)
      , fn () => "(String.implode " ^ gen (e, TyCharList, d-1) ^ ")"
      , fn () => "(String.map Char.toUpper " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(String.map Char.toLower " ^ gen (e, TyStr, d-1) ^ ")"
      (* translate: char -> string, doubles/keeps each char *)
      , fn () => "(String.translate (fn c => String.str c ^ String.str c) "
                 ^ gen (e, TyStr, d-1) ^ ")"
      (* substring slicing: bounded start/len => may raise Subscript -> wrapped *)
      , fn () => "(String.substring (" ^ gen (e, TyStr, d-1) ^ ", "
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 4, "
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 4))"
      , fn () => "(String.extract (" ^ gen (e, TyStr, d-1) ^ ", "
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 4, NONE))"
      (* Substring round-trip: full/substring/trim then back to string *)
      , fn () => "(Substring.string (Substring.full " ^ gen (e, TyStr, d-1) ^ "))"
      , fn () => "(Substring.string (Substring.dropl Char.isSpace (Substring.full "
                 ^ gen (e, TyStr, d-1) ^ ")))"
      , fn () => "(Substring.string (Substring.dropr Char.isSpace (Substring.full "
                 ^ gen (e, TyStr, d-1) ^ ")))"
      , fn () => "(Substring.string (Substring.triml (Int.abs (" ^ gen (e, TyInt, d-1)
                 ^ ") mod 4) (Substring.full " ^ gen (e, TyStr, d-1) ^ ")))"
      (* join a generated string list *)
      , fn () => "(String.concatWith \"-\" " ^ gen (e, TyStrList, d-1) ^ ")"
      , fn () => "(String.concat " ^ gen (e, TyStrList, d-1) ^ ")"
      (* APPLY a generated function returning string *)
      , fn () => "(" ^ gen (e, TyFnIS, d-1) ^ " " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyFnSS, d-1) ^ " " ^ gen (e, TyStr, d-1) ^ ")"
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

(* ---------------------------------------------------------------------- *)
(* FUNCTION-VALUED generators -- the closures dimension.                   *)
(* Each emits an expression of a MONOMORPHIC arrow type.                   *)
(* Productions: a literal fn, a captured-variable closure (genuine free    *)
(* var capture), a CURRIED function partially applied to ONE arg (returns  *)
(* a function), function COMPOSITION, and a let-bound mutual recursion.    *)
(* ---------------------------------------------------------------------- *)
and genFnII (e, d) : string =
  let
    val x = freshVar ()  (* the lambda parameter; bound int *)
    val prods =
      [ fn () => litFnII ()
      (* genuine closure: capture an outer int, body mentions x AND the capture *)
      , fn () => "(let val cap = " ^ gen (e, TyInt, d-1)
                 ^ " in (fn " ^ x ^ " => "
                 ^ gen ((x,TyInt)::e, TyInt, Int.max(1,d-1)) ^ " + cap) end)"
      (* full lambda whose body is a generated int expr mentioning x *)
      , fn () => "(fn " ^ x ^ " => "
                 ^ gen ((x,TyInt)::e, TyInt, Int.max(1,d-1)) ^ ")"
      (* CURRYING: build a 2-arg curried fn, partially apply to ONE arg =>
         result is still int->int (a returned closure). *)
      , fn () => "(let val g = (fn a => fn b => a + b * "
                 ^ litInt () ^ ") in g " ^ gen (e, TyInt, d-1) ^ " end)"
      (* COMPOSITION of two generated int->int functions *)
      , fn () => "(" ^ gen (e, TyFnII, d-1) ^ " o " ^ gen (e, TyFnII, d-1) ^ ")"
      (* mutual recursion via let..and -- even/odd-ish, fuel-bounded *)
      , fn () => "(let fun ev n = if n <= 0 then 0 else od (n-1)\n"
                 ^ "         and od n = if n <= 0 then 1 else ev (n-1)\n"
                 ^ "  in (fn " ^ x ^ " => ev (Int.abs " ^ x ^ " mod 20)) end)"
      ]
  in (pick prods) () end

and genFnIS (e, d) : string =
  let
    val x = freshVar ()
    val prods =
      [ fn () => litFnIS ()
      , fn () => "(fn " ^ x ^ " => "
                 ^ gen ((x,TyInt)::e, TyStr, Int.max(1,d-1)) ^ ")"
      (* capture a string, append the int's render *)
      , fn () => "(let val cap = " ^ gen (e, TyStr, d-1)
                 ^ " in (fn " ^ x ^ " => cap ^ Int.toString " ^ x ^ ") end)"
      (* compose: (int->int) then (int->string) *)
      , fn () => "(" ^ gen (e, TyFnIS, d-1) ^ " o " ^ gen (e, TyFnII, d-1) ^ ")"
      ]
  in (pick prods) () end

and genFnSI (e, d) : string =
  let
    val x = freshVar ()
    val prods =
      [ fn () => litFnSI ()
      , fn () => "(fn " ^ x ^ " => "
                 ^ gen ((x,TyStr)::e, TyInt, Int.max(1,d-1)) ^ ")"
      (* capture an int, add to the string size *)
      , fn () => "(let val cap = " ^ gen (e, TyInt, d-1)
                 ^ " in (fn " ^ x ^ " => String.size " ^ x ^ " + cap) end)"
      (* compose: (string->string) then (string->int) *)
      , fn () => "(" ^ gen (e, TyFnSI, d-1) ^ " o " ^ gen (e, TyFnSS, d-1) ^ ")"
      ]
  in (pick prods) () end

and genFnSS (e, d) : string =
  let
    val x = freshVar ()
    val prods =
      [ fn () => litFnSS ()
      , fn () => "(fn " ^ x ^ " => "
                 ^ gen ((x,TyStr)::e, TyStr, Int.max(1,d-1)) ^ ")"
      (* capture a string suffix *)
      , fn () => "(let val cap = " ^ gen (e, TyStr, d-1)
                 ^ " in (fn " ^ x ^ " => " ^ x ^ " ^ cap) end)"
      , fn () => "(" ^ gen (e, TyFnSS, d-1) ^ " o " ^ gen (e, TyFnSS, d-1) ^ ")"
      ];
  in (pick prods) () end;

(* ===================================================================== *)
(* 5. The per-program wrapper + result stringifier                        *)
(*    Result types are restricted to the deterministically-stringifiable  *)
(*    set (NOT functions -- you cannot print a closure).                   *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog_strings_closures.sml -- DO NOT EDIT *)\n" ^
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Chr => \"CHR\" | Option => \"OPT\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun cl2s xs = \"[\" ^ String.concatWith \",\" (List.map Char.toString xs) ^ \"]\";\n" ^
  "fun sl2s xs = \"[\" ^ String.concatWith \",\" (List.map String.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n";

(* stringify a result.  Strings/chars are C-ESCAPED (String.toString /
   Char.toString) so the @@ line stays ASCII-printable and our >=0x80-rejecting
   *output* path / any control char never trips the comparison. *)
fun resultToString (TyInt, body)      = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)     = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body)  = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)      = "wrap (fn () => String.toString (" ^ body ^ "))"
  | resultToString (TyPair, body)     = "wrap (fn () => pr2s (" ^ body ^ "))"
  | resultToString (TyChar, body)     = "wrap (fn () => Char.toString (" ^ body ^ "))"
  | resultToString (TyCharList, body) = "wrap (fn () => cl2s (" ^ body ^ "))"
  | resultToString (TyStrList, body)  = "wrap (fn () => sl2s (" ^ body ^ "))"
  (* function results cannot be printed; never chosen as a result type *)
  | resultToString (_, body)          = "wrap (fn () => \"FN\")";

(* result types: everything printable (NOT the arrow types) *)
val resultTypes =
  [TyInt, TyBool, TyIntList, TyStr, TyPair, TyChar, TyCharList, TyStrList];

fun program (i : int) : string =
  let
    val () = vctr := 0
    val rt = pick resultTypes
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
    print ("genprog_strings_closures: wrote " ^ Int.toString cfgN ^ " program(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = emitAll ();
