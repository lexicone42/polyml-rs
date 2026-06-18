(* genprog.sml -- TYPE-DIRECTED random SML PROGRAM generator (differential fuzz).
   ==========================================================================
   Run ONCE on the trusted UPSTREAM poly to emit a batch of self-contained .sml
   PROGRAM files into an output dir; each program, when piped to a poly REPL,
   prints exactly one line `@@p<i>=<wrapped result>`. diff-oracle.sh then runs
   each through OURS + UPSTREAM (native and bytecode-interp) and compares the @@
   line byte-for-byte. Byte-identical => pass.

   WHY a generator and not a fixed corpus: per-op numeric/structure fuzzers
   (fuzz_int/word/list/...) exercise ONE operation at a time. This generator
   builds WHOLE PROGRAMS -- novel control flow + FEATURE COMBINATIONS (nested
   let, if/case dispatch, recursion via the fuel'd helpers, list pipelines,
   exception flow, allocation/GC pressure) that per-function tests never reach.
   A bug that only shows in a COMBINATION (cf. the PolySubtractArbitrary bug
   that only fired on the RTS path, invisible to the opcode-path corpus) is the
   target.

   HOW IT STAYS SOUND AS A DIFFERENTIAL:
   1. TYPE-DIRECTED => well-typed BY CONSTRUCTION. gen(ty,d,env) only ever emits
      an expression of exactly `ty`, drawing sub-expressions of the required
      types recursively, or (at d<=0) a LEAF: a literal or an in-scope variable
      of that type from the typed `env`. No type errors => both sides compile +
      run identically => any @@ divergence is a genuine OUR-side faithfulness
      bug, never a test artifact.
   2. DETERMINISTIC LCG (same MMIX constants as the existing fuzz_*.sml) -- the
      generator is reproducible; rerun with the same seed => byte-identical
      program files. (The generated PROGRAMS are themselves deterministic too:
      no input, no clock, no randomness at run time.)
   3. EVERY result is wrapped: an exception becomes a COMPARABLE TOKEN
      ("OVF"/"DIV"/"SUB"/...). Both sides raising the same exn => they agree.
   4. BOUNDED: expression depth, list lengths, tabulate counts, and recursion
      fuel are all capped, so programs terminate fast and stay small. The
      harness timeout/max-steps is only a backstop.
   5. OUTPUT IS TOTALLY STRINGIFIED + DETERMINISTIC: Int.toString / Bool.toString
      / a fixed list-stringifier. NO Real formatting, NO ref/exn/function
      PRINTING (we print computed VALUES, never addresses), NO andb/orb on big
      IntInf (the known stage-0 quirk). int / bool / int list / string /
      (int*int) results only.

   USAGE (run on the trusted UPSTREAM poly):
     /tmp/polybuild/poly < tools/diff-corpus-gen/genprog.sml
   Env (read via OS.Process.getEnv):
     GENPROG_SEED   (default 1)         -- LCG seed; change => different batch.
     GENPROG_N      (default 30)        -- number of program files to emit.
     GENPROG_OUT    (default /tmp/genprog) -- output directory (created if absent).
     GENPROG_DEPTH  (default 5)         -- max expression depth.
     GENPROG_PREFIX (default p)         -- file/label prefix: <PREFIX><i>.sml.
   Then:
     tools/diff-oracle.sh --dir /tmp/genprog
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir /tmp/genprog
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
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "p");

(* ===================================================================== *)
(* 1. The LCG (Knuth/MMIX constants; Word is 63-bit in default-int config) *)
(*    Same PRNG as the existing fuzz_*.sml so the idiom is familiar.       *)
(* ===================================================================== *)
val s = ref (Word.fromInt cfgSeed + 0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
fun nxt () = Word.toInt (Word.>> (step (), 0w11));   (* nonnegative draw *)
fun upto n = if n <= 0 then 0 else nxt () mod n;       (* in [0,n) *)
fun bit () = upto 2;
fun chance k = upto k = 0;                             (* 1-in-k *)

(* ===================================================================== *)
(* 2. The typed environment                                               *)
(*    A small association list: variable name -> its TYPE. gen draws LEAF  *)
(*    variables from here, and `let` extends it. Types are a closed set.   *)
(* ===================================================================== *)
datatype ty = TyInt | TyBool | TyIntList | TyStr | TyPair;  (* TyPair = int*int *)

fun tyName TyInt = "int"
  | tyName TyBool = "bool"
  | tyName TyIntList = "int list"
  | tyName TyStr = "string"
  | tyName TyPair = "int*int";

(* env = (name, ty) list, innermost first *)
type env = (string * ty) list;

(* fresh variable names, monotonic across one program *)
val vctr = ref 0;
fun freshVar () = (vctr := !vctr + 1; "v" ^ Int.toString (!vctr));

(* all in-scope vars of a given type *)
fun varsOf (e : env, t : ty) : string list =
  List.map #1 (List.filter (fn (_, t') => t' = t) e);

(* pick a random element of a non-empty list *)
fun pick xs = List.nth (xs, upto (List.length xs));

(* ===================================================================== *)
(* 3. Leaf generators (depth-0 terminals; always type-correct)            *)
(* ===================================================================== *)
(* small int literal, including negatives, kept modest so arithmetic on
   them rarely overflows by accident (overflow IS reachable via combination
   and is wrapped, so it's a comparable token, not a divergence). *)
fun litInt () =
  let val n = upto 21 - 10               (* -10..10 *)
  in if n < 0 then "(~" ^ Int.toString (~n) ^ ")" else Int.toString n end;

fun litBool () = if bit () = 0 then "true" else "false";

(* a small fixed-length int list literal *)
fun litIntList () =
  let val k = upto 5                      (* 0..4 elements *)
      fun elems 0 = []
        | elems i = litInt () :: elems (i - 1)
  in "[" ^ String.concatWith ", " (elems k) ^ "]" end;

(* a short string literal from a safe ASCII alphabet (printable, no escapes,
   no chars >= 0x80 -- our string lexer rejects those, and they're not the
   point). *)
val alpha = "abcdefghijklmnopqrstuvwxyz0123456789 ";
fun litChar () = String.str (String.sub (alpha, upto (String.size alpha)));
fun litStr () =
  let val k = upto 6                      (* 0..5 chars *)
      fun cs 0 = "" | cs i = litChar () ^ cs (i - 1)
  in "\"" ^ cs k ^ "\"" end;

fun litPair () = "(" ^ litInt () ^ ", " ^ litInt () ^ ")";

(* a depth-0 LEAF of type t: an in-scope variable if one exists (50/50), else
   a literal. ALWAYS returns a well-typed expression of type t. *)
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
            | TyPair => litPair ())
  end;

(* ===================================================================== *)
(* 4. The type-directed core: gen (e, t, d)                                *)
(*    Emit an expression of type t under env e at depth budget d.          *)
(*    d<=0  => leaf. Otherwise pick a random PRODUCTION for t whose        *)
(*    sub-expressions recurse at d-1. Mutually recursive across types.     *)
(* ===================================================================== *)
fun gen (e : env, t : ty, d : int) : string =
  if d <= 0 then leaf (e, t)
  else case t of
           TyInt     => genInt (e, d)
         | TyBool    => genBool (e, d)
         | TyIntList => genList (e, d)
         | TyStr     => genStr (e, d)
         | TyPair    => genPair (e, d)

(* ---- a LET that binds a fresh var of a random type, body has type t ---- *)
and genLet (e : env, t : ty, d : int) : string =
  let val bt = pick [TyInt, TyBool, TyIntList, TyStr, TyPair]
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
      , fn () => "(Int.max (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(Int.min (" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ "))"
      , fn () => "(~ " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Int.abs " ^ gen (e, TyInt, d-1) ^ ")"
      (* div/mod can raise Div -- wrapped at the program top, so a Div on
         BOTH sides agrees; we still keep them rare to vary control flow *)
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " div " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyInt, d-1) ^ " mod " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(List.length " ^ gen (e, TyIntList, d-1) ^ ")"
      (* fold a list down to an int -- exercises List.foldl + a closure *)
      , fn () => "(List.foldl (fn (a,b) => a + b) 0 " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      (* a small fuel'd recursive sum 0..n via a local fun -- recursion + TCO *)
      , fn () => "(let fun f n acc = if n <= 0 then acc else f (n-1) (acc+n) in f ("
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 30) 0 end)"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      (* case over a list: empty vs head::tail -- datatype-ish dispatch *)
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
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " andalso " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyBool, d-1) ^ " orelse " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(not " ^ gen (e, TyBool, d-1) ^ ")"
      , fn () => "(List.null " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(" ^ gen (e, TyStr, d-1) ^ " = " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(List.exists (fn x => x > 0) " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.all (fn x => x < 100) " ^ gen (e, TyIntList, d-1) ^ ")"
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
      , fn () => "(List.map (fn x => " ^ genIntInX (e, d-1) ^ ") " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.filter (fn x => x mod 2 = 0) " ^ gen (e, TyIntList, d-1) ^ ")"
      (* bounded tabulate: count = |gen-int| mod 12, so <= 11 elements *)
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
      , fn () => "(String.substring (" ^ gen (e, TyStr, d-1)
                 ^ ", 0, 1))"   (* may raise Subscript -> wrapped token *)
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
                 ^ " in (#2 p, #1 p) end)"   (* swap *)
      , fn () => genIf (e, TyPair, d)
      , fn () => genLet (e, TyPair, d)
      ]
  in (pick prods) () end

(* a small int-valued expression mentioning the lambda-bound `x : int`
   (used inside List.map's fn x => ...). We bind x into a fresh env so the
   recursive generator can legally use it as a leaf. *)
and genIntInX (e, d) : string =
  gen (("x", TyInt) :: e, TyInt, Int.max (1, d))

(* int-valued expression that may mention the tabulate index `i : int` *)
and genIntInI (e, d) : string =
  gen (("i", TyInt) :: e, TyInt, Int.max (1, d));

(* ===================================================================== *)
(* 5. The per-program wrapper + result stringifier                        *)
(*    Each program: define `wrap` (exn -> token) + `il2s` (int list ->     *)
(*    string) + `pr2s` (pair -> string), compute ONE top-level expression  *)
(*    of a chosen result type, stringify it, and print @@<prefix><i>=<...>. *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog.sml -- DO NOT EDIT *)\n" ^
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n";

(* the to-string call appropriate for a result type, applied to a thunk so it
   is inside `wrap` -- an exception during EVALUATION becomes a token. *)
fun resultToString (TyInt, body)     = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)    = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body) = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)     = "wrap (fn () => (" ^ body ^ "))"
  | resultToString (TyPair, body)    = "wrap (fn () => pr2s (" ^ body ^ "))";

(* build the full source text of program #i *)
fun program (i : int) : string =
  let
    val () = vctr := 0   (* reset fresh-var counter per program *)
    val rt = pick [TyInt, TyBool, TyIntList, TyStr, TyPair]
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
    print ("genprog: wrote " ^ Int.toString cfgN ^ " program(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = emitAll ();
