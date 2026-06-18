(* genprog_lists_hof.sml -- TYPE-DIRECTED random SML PROGRAM generator.
   DIMENSION = lists_hof: lists + tuples + higher-order functions
   (map/foldl/foldr/filter/partition/exists/all/tabulate/find/mapPartial/
   takeWhile/dropWhile) + ANONYMOUS FNS with GENERATED bodies + pattern
   matching on lists/tuples (multi-arm case, nested patterns, as-patterns,
   tuple destructuring let) + list-comprehension-style pipelines + ListPair
   (zip/unzip). Bounded list lengths.
   ==========================================================================
   This is a SEAT of the shared genprog framework (tools/diff-corpus-gen/
   genprog.sml). It keeps the framework invariants UNCHANGED -- the same LCG
   (seeded from GENPROG_SEED), the same wrap-exn-to-token discipline, the same
   deterministic stringify, the same ASCII-clean output -- and ADDS the typed
   productions / new ty constructors that exercise the lists_hof dimension.

   WHY the lists_hof seat: per-op fuzzers (fuzz_list.sml) test ONE List op at a
   time with a FIXED callback. This seat generates the CALLBACK BODIES too
   (anonymous fns whose int/bool bodies are themselves type-directed), nests
   HOFs (map over a filter over a tabulate), threads results through tuples and
   pattern matches, and combines all of it into WHOLE PROGRAMS. The combination
   -- a closure capturing an outer let var, passed to foldl over a tabulate'd
   list, whose result feeds a tuple destructure -- is what per-op tests never
   reach.

   SOUNDNESS (identical to the base framework):
   1. TYPE-DIRECTED => well-typed BY CONSTRUCTION. Every production emits an
      expression of exactly the requested type; every lambda binds its argument
      into the env before generating its (typed) body, so the body is legal.
   2. DETERMINISTIC LCG; reproducible per seed.
   3. EVERY result wrapped: exn -> comparable token. Both sides raising the same
      exn => agree.
   4. BOUNDED: depth, list lengths, tabulate counts, recursion fuel all capped.
   5. TOTALLY STRINGIFIED + DETERMINISTIC: int / bool / int list / string /
      (int*int) / (int list * int list) results only. NO Real fmt, NO ref/exn/fn
      printing, NO andb/orb on big IntInf.

   USAGE (run on the trusted UPSTREAM poly):
     GENPROG_SEED=42 GENPROG_N=400 GENPROG_OUT=tools/diff-corpus-gen/out/lists_hof \
       GENPROG_PREFIX=genprog_lists_hof_ /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_lists_hof.sml
   Then:
     tools/diff-oracle.sh --dir tools/diff-corpus-gen/out/lists_hof
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir tools/diff-corpus-gen/out/lists_hof
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
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog_lists_hof");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "lh");
(* GENPROG_BUNDLE=<path>: when set, emit ONE self-contained .sml file at <path>
   with a single shared preamble + N labelled print lines (the existing
   fuzz_*.sml corpus idiom), instead of N separate per-program files in cfgOut.
   This amortizes our ~1.2s checkpoint-load startup across all N programs so the
   batch is cheap enough for CI (regression.sh runs the whole corpus). Each
   program body is a single EXPRESSION (no top-level decls), so concatenating
   them under one preamble is sound. *)
val cfgBundle = getStr ("GENPROG_BUNDLE", "");

(* ===================================================================== *)
(* 1. The LCG (Knuth/MMIX constants; same PRNG as the base framework)     *)
(* ===================================================================== *)
val s = ref (Word.fromInt cfgSeed + 0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
fun nxt () = Word.toInt (Word.>> (step (), 0w11));
fun upto n = if n <= 0 then 0 else nxt () mod n;
fun bit () = upto 2;
fun chance k = upto k = 0;

(* ===================================================================== *)
(* 2. The typed environment                                               *)
(*    Closed type set extended for the lists_hof dimension:               *)
(*      TyPairList = int list * int list  (the result of List.partition)  *)
(* ===================================================================== *)
datatype ty = TyInt | TyBool | TyIntList | TyStr | TyPair | TyPairList;

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
  let val k = upto 6                      (* 0..5 elements *)
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
fun litPairList () = "(" ^ litIntList () ^ ", " ^ litIntList () ^ ")";

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
            | TyPairList => litPairList ())
  end;

(* ===================================================================== *)
(* 4. The type-directed core                                              *)
(* ===================================================================== *)
fun gen (e : env, t : ty, d : int) : string =
  if d <= 0 then leaf (e, t)
  else case t of
           TyInt      => genInt (e, d)
         | TyBool     => genBool (e, d)
         | TyIntList  => genList (e, d)
         | TyStr      => genStr (e, d)
         | TyPair     => genPair (e, d)
         | TyPairList => genPairList (e, d)

and genLet (e : env, t : ty, d : int) : string =
  let val bt = pick [TyInt, TyBool, TyIntList, TyStr, TyPair, TyPairList]
      val x = freshVar ()
      val rhs = gen (e, bt, d - 1)
      val e' = (x, bt) :: e
      val body = gen (e', t, d - 1)
  in "(let val " ^ x ^ " = " ^ rhs ^ " in " ^ body ^ " end)" end

and genIf (e : env, t : ty, d : int) : string =
  "(if " ^ gen (e, TyBool, d - 1) ^ " then " ^ gen (e, t, d - 1)
  ^ " else " ^ gen (e, t, d - 1) ^ ")"

(* ----------------------------------------------------------------- *)
(* GENERATED LAMBDA BODIES                                            *)
(* genFnBody (e, paramName, paramTy, bodyTy, d): generate the BODY of *)
(* a lambda `fn <param> => <body>` whose argument <param>:paramTy is  *)
(* in scope, returning bodyTy. We inject the binder into env so the   *)
(* recursive generator may legally use it as a leaf. The lambda's     *)
(* arg is always an int (list elements are ints) -- but the body type *)
(* varies: int (map's a), bool (filter/exists/all predicate), etc.    *)
(* ----------------------------------------------------------------- *)
and genFnBody (e : env, pn : string, pt : ty, bt : ty, d : int) : string =
  gen ((pn, pt) :: e, bt, Int.max (1, d))

(* a `fn x => <int-body mentioning x>` -- for map *)
and lamIntToInt (e, d) =
  "(fn x => " ^ genFnBody (e, "x", TyInt, TyInt, d) ^ ")"
(* a `fn x => <bool-body mentioning x>` -- for filter/exists/all/partition *)
and lamIntToBool (e, d) =
  "(fn x => " ^ genFnBody (e, "x", TyInt, TyBool, d) ^ ")"
(* a `fn x => <string-body mentioning x>` -- for map-to-string-list-ish *)
and lamIntToStr (e, d) =
  "(fn x => " ^ genFnBody (e, "x", TyInt, TyStr, d) ^ ")"
(* a `fn (a,b) => <int>` folder: a = element, b = accumulator (both int) *)
and lamFoldInt (e, d) =
  let val acc = freshVar ()
      val e' = (acc, TyInt) :: ("x", TyInt) :: e
  in "(fn (x, " ^ acc ^ ") => " ^ gen (e', TyInt, Int.max (1, d)) ^ ")" end
(* a `fn (a,b) => <int list>` folder building a list *)
and lamFoldList (e, d) =
  let val acc = freshVar ()
      val e' = (acc, TyIntList) :: ("x", TyInt) :: e
  in "(fn (x, " ^ acc ^ ") => " ^ gen (e', TyIntList, Int.max (1, d)) ^ ")" end
(* a `fn x => SOME/NONE` mapPartial callback *)
and lamMapPartial (e, d) =
  "(fn x => if " ^ genFnBody (e, "x", TyInt, TyBool, d)
  ^ " then SOME (" ^ genFnBody (e, "x", TyInt, TyInt, d) ^ ") else NONE)"
(* tabulate index fn: int -> int mentioning i *)
and lamTabulate (e, d) =
  "(fn i => " ^ genFnBody (e, "i", TyInt, TyInt, d) ^ ")"

(* ----------------------------------------------------------------- *)
(* INT productions: many surfaces reduce a list/tuple/HOF to an int.  *)
(* ----------------------------------------------------------------- *)
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
      (* --- list -> int reductions, the core of the dimension --- *)
      , fn () => "(List.length " ^ gen (e, TyIntList, d-1) ^ ")"
      (* foldl with a GENERATED folder body (closure over outer vars) *)
      , fn () => "(List.foldl " ^ lamFoldInt (e, d-1) ^ " "
                 ^ gen (e, TyInt, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.foldr " ^ lamFoldInt (e, d-1) ^ " "
                 ^ gen (e, TyInt, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* List.nth -- may raise Subscript -> wrapped token *)
      , fn () => "(List.nth (" ^ gen (e, TyIntList, d-1) ^ ", Int.abs ("
                 ^ gen (e, TyInt, d-1) ^ ") mod 7))"
      (* hd / last -- may raise Empty -> wrapped *)
      , fn () => "(hd " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.last " ^ gen (e, TyIntList, d-1) ^ ")"
      (* getOpt over List.find -- option flow + closure *)
      , fn () => "(getOpt (List.find " ^ lamIntToBool (e, d-1) ^ " "
                 ^ gen (e, TyIntList, d-1) ^ ", 0))"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      (* fuel'd recursive sum 0..n -- recursion + TCO *)
      , fn () => "(let fun f n acc = if n <= 0 then acc else f (n-1) (acc+n) in f ("
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 30) 0 end)"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      (* MULTI-ARM list pattern match: nested patterns + wildcard + as-pattern *)
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => 0"
                 ^ " | [a] => a"
                 ^ " | [a, b] => a + b"
                 ^ " | (a :: b :: _) => a - b)"
      (* tuple destructuring case (pair-of-lists) *)
      , fn () => "(case " ^ gen (e, TyPairList, d-1)
                 ^ " of (xs, ys) => List.length xs - List.length ys)"
      ]
  in (pick prods) () end

and genBool (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ " < " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " <= " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " = " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " > " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " andalso " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " orelse " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(not " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(List.null " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStr, d-1) ^ " = " ^ gen (e, TyStr, d-1) ^ ")"
      (* list structural equality -- exercises the polymorphic = on lists *)
      , fn () => "(" ^ gen (e, TyIntList, d-1) ^ " = " ^ gen (e, TyIntList, d-1) ^ ")"
      (* exists/all with GENERATED predicate bodies (closures) *)
      , fn () => "(List.exists " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.all " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* membership via List.find isSome *)
      , fn () => "(isSome (List.find " ^ lamIntToBool (e, d-1) ^ " "
                 ^ gen (e, TyIntList, d-1) ^ "))"
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
      (* map with a GENERATED int-body lambda *)
      , fn () => "(List.map " ^ lamIntToInt (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* filter with a GENERATED predicate *)
      , fn () => "(List.filter " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* mapPartial with a GENERATED SOME/NONE callback *)
      , fn () => "(List.mapPartial " ^ lamMapPartial (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* foldr building a list (op:: surface) *)
      , fn () => "(List.foldr " ^ lamFoldList (e, d-1) ^ " [] " ^ gen (e, TyIntList, d-1) ^ ")"
      (* bounded tabulate: count = |int| mod 12 (<=11 elements), generated body *)
      , fn () => "(List.tabulate (Int.abs (" ^ gen (e, TyInt, d-1)
                 ^ ") mod 12, " ^ lamTabulate (e, d-1) ^ "))"
      (* take / drop -- may raise Subscript -> wrapped *)
      , fn () => "(List.take (" ^ gen (e, TyIntList, d-1) ^ ", Int.abs ("
                 ^ gen (e, TyInt, d-1) ^ ") mod 7))"
      , fn () => "(List.drop (" ^ gen (e, TyIntList, d-1) ^ ", Int.abs ("
                 ^ gen (e, TyInt, d-1) ^ ") mod 7))"
      (* concat of two lists via List.concat *)
      , fn () => "(List.concat [" ^ gen (e, TyIntList, d-1) ^ ", "
                 ^ gen (e, TyIntList, d-1) ^ "])"
      (* multi-arm pattern match producing a list (tail/cons restructure) *)
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => []"
                 ^ " | (a :: rest) => rest @ [a])"   (* rotate-left *)
      (* extract one component of a pair-of-lists *)
      , fn () => "(#1 " ^ gen (e, TyPairList, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPairList, d-1) ^ ")"
      (* ListPair.unzip then take a side -- zip/unzip round-trip surface *)
      , fn () => "(#1 (ListPair.unzip (ListPair.zip (" ^ gen (e, TyIntList, d-1)
                 ^ ", " ^ gen (e, TyIntList, d-1) ^ "))))"
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
      , fn () => "(String.substring (" ^ gen (e, TyStr, d-1) ^ ", 0, 1))"
      , fn () => "(String.map Char.toUpper " ^ gen (e, TyStr, d-1) ^ ")"
      (* int list -> string via map+concatWith (a classic pipeline) *)
      , fn () => "(String.concatWith \"-\" (List.map Int.toString "
                 ^ gen (e, TyIntList, d-1) ^ "))"
      (* map a generated string-body over a list then concat *)
      , fn () => "(String.concat (List.map " ^ lamIntToStr (e, d-1)
                 ^ " " ^ gen (e, TyIntList, d-1) ^ "))"
      , fn () => genIf (e, TyStr, d)
      , fn () => genLet (e, TyStr, d)
      ]
  in (pick prods) () end

and genPair (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(let val p = " ^ gen (e, TyPair, d-1)
                 ^ " in (#2 p, #1 p) end)"   (* swap *)
      (* tuple destructuring let-pattern: (a, b) = pair *)
      , fn () => "(let val (a, b) = " ^ gen (e, TyPair, d-1)
                 ^ " in (b, a) end)"
      (* (length, sum) of a generated list -- pair-building pipeline *)
      , fn () => "(let val xs = " ^ gen (e, TyIntList, d-1)
                 ^ " in (List.length xs, List.foldl (fn (a,b) => a + b) 0 xs) end)"
      , fn () => genIf (e, TyPair, d)
      , fn () => genLet (e, TyPair, d)
      ]
  in (pick prods) () end

and genPairList (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyIntList, d-1) ^ ", " ^ gen (e, TyIntList, d-1) ^ ")"
      (* List.partition with a GENERATED predicate -- yields (yes, no) *)
      , fn () => "(List.partition " ^ lamIntToBool (e, d-1) ^ " "
                 ^ gen (e, TyIntList, d-1) ^ ")"
      (* ListPair.unzip of a zip -- pair-of-lists surface *)
      , fn () => "(ListPair.unzip (ListPair.zip (" ^ gen (e, TyIntList, d-1)
                 ^ ", " ^ gen (e, TyIntList, d-1) ^ ")))"
      (* split via take/drop at a bounded index *)
      , fn () => "(let val xs = " ^ gen (e, TyIntList, d-1)
                 ^ " val k = Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 7"
                 ^ " in (List.take (xs, Int.min (k, List.length xs)),"
                 ^ " List.drop (xs, Int.min (k, List.length xs))) end)"
      (* swap the two sublists -- tuple destructure *)
      , fn () => "(let val (p, q) = " ^ gen (e, TyPairList, d-1)
                 ^ " in (q, p) end)"
      , fn () => genIf (e, TyPairList, d)
      , fn () => genLet (e, TyPairList, d)
      ]
  in (pick prods) () end;

(* ===================================================================== *)
(* 5. The per-program wrapper + result stringifier                        *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog_lists_hof.sml -- DO NOT EDIT *)\n" ^
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n" ^
  "fun pl2s (xs,ys) = \"(\" ^ il2s xs ^ \",\" ^ il2s ys ^ \")\";\n";

fun resultToString (TyInt, body)      = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)     = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body)  = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)      = "wrap (fn () => (" ^ body ^ "))"
  | resultToString (TyPair, body)     = "wrap (fn () => pr2s (" ^ body ^ "))"
  | resultToString (TyPairList, body) = "wrap (fn () => pl2s (" ^ body ^ "))";

(* result types are biased toward the dimension: lists / pair-of-lists / pairs
   get extra weight so most programs END in a list-shaped value. *)
val resultTypes =
  [ TyIntList, TyIntList, TyIntList
  , TyPairList, TyPairList
  , TyPair
  , TyInt, TyInt
  , TyBool
  , TyStr ];

(* the single print statement for program #i (no preamble) -- shared by the
   per-file and bundle emitters so both consume the SAME LCG sequence. *)
fun programLine (i : int) : string =
  let
    val () = vctr := 0
    val rt = pick resultTypes
    val body = gen ([], rt, cfgDepth)
    val label = cfgPrefix ^ Int.toString i
    val rs = resultToString (rt, body)
  in
    "val () = print (\"@@" ^ label ^ "=\" ^ (" ^ rs ^ ") ^ \"\\n\");\n"
  end;

(* a standalone per-file program: preamble + one print line *)
fun program (i : int) : string = preamble ^ programLine i;

(* ===================================================================== *)
(* 6. Emit N program files into cfgOut                                     *)
(* ===================================================================== *)
fun ensureDir d =
  if OS.FileSys.access (d, []) then ()
  else OS.FileSys.mkDir d;

fun writeFile (path, contents) =
  let val os = TextIO.openOut path
  in TextIO.output (os, contents); TextIO.closeOut os end;

(* per-file emit: N separate .sml files (one program each) under cfgOut *)
fun emitFiles () =
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
    print ("genprog_lists_hof: wrote " ^ Int.toString cfgN ^ " file(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

(* bundle emit: ONE self-contained .sml file (shared preamble + N print lines)
   at cfgBundle. The corpus idiom -- amortizes startup across all N programs. *)
fun emitBundle () =
  let
    val hdr =
      "(* GENERATED by tools/diff-corpus-gen/genprog_lists_hof.sml -- DO NOT EDIT.\n" ^
      "   lists_hof dimension: type-directed whole-program differential fuzz\n" ^
      "   (lists + tuples + higher-order fns + pattern matching + pipelines).\n" ^
      "   Regenerate: GENPROG_SEED=" ^ Int.toString cfgSeed ^ " GENPROG_N=" ^ Int.toString cfgN ^
      " GENPROG_DEPTH=" ^ Int.toString cfgDepth ^ " GENPROG_PREFIX=" ^ cfgPrefix ^ "\n" ^
      "     GENPROG_BUNDLE=<path> /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_lists_hof.sml\n" ^
      "   " ^ Int.toString cfgN ^ " programs; each prints one @@" ^ cfgPrefix ^ "<i>=<wrapped result>. *)\n"
    fun loop (i, acc) = if i >= cfgN then acc else loop (i + 1, acc ^ programLine i)
    val body = loop (0, "")
  in
    writeFile (cfgBundle, hdr ^ preamble ^ body);
    print ("genprog_lists_hof: wrote bundle of " ^ Int.toString cfgN ^ " program(s) to " ^ cfgBundle
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = if cfgBundle <> "" then emitBundle () else emitFiles ();
