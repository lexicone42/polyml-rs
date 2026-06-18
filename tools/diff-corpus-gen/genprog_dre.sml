(* genprog_dre.sml -- TYPE-DIRECTED random SML PROGRAM generator, DIMENSION =
   datatypes_rec_exn.  (differential fuzz; sibling of genprog.sml)
   ==========================================================================
   Run ONCE on the trusted UPSTREAM poly to emit a batch of self-contained .sml
   PROGRAM files; each, when piped to a poly REPL, prints exactly one line
   `@@<label>=<wrapped result>`. diff-oracle.sh runs each through OURS +
   UPSTREAM (native and bytecode-interp) and compares the @@ line byte-for-byte.

   WHY THIS DIMENSION: per-op fuzzers (fuzz_int/list/string/...) exercise ONE
   operation at a time, and the base genprog.sml covers list/int/bool/string/
   pair control flow.  NEITHER reaches the COMBINATION this driver targets:

     USER DATATYPES (tree/option-like/either-like)
       + RECURSIVE user functions over them (bounded fuel, so they terminate)
       + RICH PATTERN MATCHING (nested patterns, as-patterns, wildcard, literal
         patterns, multi-arm case -> the CASE / CASE16 opcode family)
       + EXCEPTION FLOW THROUGH COMPILED RECURSIVE CODE: declare `exception
         E of int`, raise CONDITIONALLY inside the recursive functions / inside
         case arms / through List.map callbacks, HANDLE with typed `handle E x
         => ...`, RE-RAISE, NEST handlers.

   This is exactly the "exception-unwinding-bug territory" + the CASE16 /
   constructor-tag-dispatch territory called out in the project notes: an exn
   raised deep in a recursive call and caught several frames up, possibly out
   of a higher-order callback, is the path that historically tripped the "exn
   packet called as a closure" interpreter halt and that the JIT differential's
   interp-first short-circuit can MASK.  A wrong-VALUE-on-exn-path bug, or a
   constructor-tag mis-dispatch, would show as an @@ divergence here.

   SOUNDNESS (same discipline as genprog.sml):
   1. TYPE-DIRECTED => well-typed BY CONSTRUCTION.  gen(e,t,d) only ever emits
      an expression of exactly `t`.  The user datatypes/exceptions are FIXED and
      emitted verbatim in the preamble, so every constructor/handler the
      generator references is in scope.  No type errors => both sides compile +
      run identically => any @@ divergence is a genuine OUR-side faithfulness
      bug.
   2. DETERMINISTIC LCG (MMIX constants, same as fuzz_*.sml + genprog.sml).
   3. EVERY result wrapped: an exception that ESCAPES the program body becomes a
      COMPARABLE TOKEN ("OVF"/"DIV"/"USR"/...).  Both sides => agree.  (We add
      "USR" for our own user exceptions so an uncaught user exn is comparable.)
   4. BOUNDED: expression depth, datatype build depth, list lengths, and the
      recursion FUEL are all capped, so programs terminate fast.
   5. OUTPUT TOTALLY STRINGIFIED + DETERMINISTIC: every datatype value is folded
      to an int/bool/string before printing.  NO Real fmt, NO ref/exn/function
      PRINTING (we print computed VALUES, never addresses), NO andb/orb on big
      IntInf.

   USAGE (run on the trusted UPSTREAM poly):
     /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_dre.sml
   Env (read via OS.Process.getEnv):
     GENPROG_SEED   (default 1)
     GENPROG_N      (default 30)
     GENPROG_OUT    (default /tmp/genprog_dre)
     GENPROG_DEPTH  (default 5)
     GENPROG_PREFIX (default genprog_dre_)
   Then:
     tools/diff-oracle.sh --dir <GENPROG_OUT>
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir <GENPROG_OUT>
*)

(* ===================================================================== *)
(* 0. Config (env-driven)                                                 *)
(* ===================================================================== *)
fun getInt (name, dflt) =
  case OS.Process.getEnv name of
      NONE => dflt
    | SOME s => (case Int.fromString s of SOME n => n | NONE => dflt);
fun getStr (name, dflt) =
  case OS.Process.getEnv name of NONE => dflt | SOME s => s;

val cfgSeed   = getInt ("GENPROG_SEED", 1);
val cfgN      = getInt ("GENPROG_N", 30);
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog_dre");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "genprog_dre_");

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
(* 2. Types.  The base set from genprog.sml PLUS the new user datatypes.   *)
(*    TyTree    = `itree`   (datatype itree = Leaf of int | Br of itree*itree) *)
(*    TyOpt     = `ibox`    (datatype ibox  = Non | Som of int)               *)
(*    TyEither  = `ieither` (datatype ieither = Lft of int | Rgt of string)   *)
(* ===================================================================== *)
datatype ty = TyInt | TyBool | TyIntList | TyStr | TyPair
            | TyTree | TyOpt | TyEither;

(* env = (name, ty) list, innermost first *)
type env = (string * ty) list;

val vctr = ref 0;
fun freshVar () = (vctr := !vctr + 1; "v" ^ Int.toString (!vctr));

fun varsOf (e : env, t : ty) : string list =
  List.map #1 (List.filter (fn (_, t') => t' = t) e);

fun pick xs = List.nth (xs, upto (List.length xs));

(* all generatable result types -- used for `let` rhs and program result type. *)
val allTys = [TyInt, TyBool, TyIntList, TyStr, TyPair, TyTree, TyOpt, TyEither];

(* ===================================================================== *)
(* 3. Leaf generators (depth-0 terminals; always type-correct)            *)
(* ===================================================================== *)
fun litInt () =
  let val n = upto 21 - 10
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

(* leaf datatype literals (depth-0 terminals for the user types) *)
fun litTree () = "(Leaf " ^ litInt () ^ ")";
fun litOpt () = if bit () = 0 then "Non" else "(Som " ^ litInt () ^ ")";
fun litEither () =
  if bit () = 0 then "(Lft " ^ litInt () ^ ")" else "(Rgt " ^ litStr () ^ ")";

(* a depth-0 LEAF of type t: an in-scope variable (50/50), else a literal. *)
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
            | TyTree => litTree ()
            | TyOpt => litOpt ()
            | TyEither => litEither ())
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
         | TyTree    => genTree (e, d)
         | TyOpt     => genOpt (e, d)
         | TyEither  => genEither (e, d)

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

(* ---- a HANDLE wrapping an expr of type t.  The body may raise one of our
        user exceptions; the handler returns a same-typed expr.  We always
        give a TYPED handler arm for E1 (carries int) and a catch-all.  This is
        exn flow THROUGH whatever the body computes, caught and a value of the
        SAME type returned -- a value-on-exn-path test.  We choose handler
        forms that re-raise or nest for some fraction. ---- *)
and genHandle (e : env, t : ty, d : int) : string =
  let val body = gen (e, t, d - 1)
      val x = freshVar ()
      val alt = gen (e, t, d - 1)
      val alt2 = gen (e, t, d - 1)
  in
    case upto 3 of
        (* typed handler: bind the carried int, then build a t-valued expr that
           may mention it (x : int in scope for the arm). *)
        0 => "(" ^ body ^ " handle E1 " ^ x ^ " => "
             ^ gen ((x, TyInt) :: e, t, d - 1) ^ " | _ => " ^ alt ^ ")"
        (* nested handlers: inner catches E2, outer catches E1/anything. *)
      | 1 => "((" ^ body ^ " handle E2 => " ^ alt ^ ") handle E1 "
             ^ x ^ " => " ^ gen ((x, TyInt) :: e, t, d - 1)
             ^ " | _ => " ^ alt2 ^ ")"
        (* re-raise: inner handler catches E1 then re-raises a DIFFERENT exn;
           outer catches it.  Exercises raise-from-within-a-handler. *)
      | _ => "((" ^ body ^ " handle E1 " ^ x ^ " => raise E2) handle E2 => "
             ^ alt ^ " | _ => " ^ alt2 ^ ")"
  end

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
      , fn () => "(List.length " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.foldl (fn (a,b) => a + b) 0 " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      (* ---- DIMENSION-SPECIFIC: fold a TREE to an int via a RECURSIVE,
              FUEL'D user function that pattern-matches and may RAISE deep in
              recursion (E1 on a Leaf whose value is negative), caught here. ---- *)
      , fn () => "(treeSum " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => "(treeDepth " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => "(treeProd " ^ gen (e, TyTree, d-1) ^ ")"   (* may raise/handle inside *)
      (* deconstruct an option via case (nested patterns + literal pattern) *)
      , fn () => "(case " ^ gen (e, TyOpt, d-1)
                 ^ " of Non => 0 | Som 0 => 100 | Som n => n)"
      (* deconstruct an either: tag dispatch -> int *)
      , fn () => "(case " ^ gen (e, TyEither, d-1)
                 ^ " of Lft n => n | Rgt s => String.size s)"
      (* unwrap an option with a user exn on NONE, caught locally *)
      , fn () => "((case " ^ gen (e, TyOpt, d-1)
                 ^ " of Som n => n | Non => raise E1 (~1)) handle E1 k => k)"
      , fn () => genHandle (e, TyInt, d)
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
      (* ---- DIMENSION-SPECIFIC: option/either tag tests via case ---- *)
      , fn () => "(case " ^ gen (e, TyOpt, d-1)
                 ^ " of Non => false | Som _ => true)"
      , fn () => "(case " ^ gen (e, TyEither, d-1)
                 ^ " of Lft _ => true | Rgt _ => false)"
      (* membership-in-tree: a recursive predicate over the tree *)
      , fn () => "(treeAny " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => genHandle (e, TyBool, d)
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
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => [] | _ :: t => t)"
      , fn () => genIf (e, TyIntList, d)
      , fn () => genLet (e, TyIntList, d)
      (* ---- DIMENSION-SPECIFIC: flatten a tree (in-order) to a list ---- *)
      , fn () => "(treeFlat " ^ gen (e, TyTree, d-1) ^ ")"
      (* List.map callback that RAISES on a negative element; caught here so
         the whole map either completes or yields []. Exn through a higher-order
         callback + recursion (map is recursive in the basis). *)
      , fn () => "((List.map (fn x => if x < 0 then raise E1 x else x + 1) "
                 ^ gen (e, TyIntList, d-1) ^ ") handle E1 _ => [])"
      , fn () => genHandle (e, TyIntList, d)
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
      , fn () => "(String.concatWith \"-\" (List.map Int.toString "
                 ^ gen (e, TyIntList, d-1) ^ "))"
      , fn () => genIf (e, TyStr, d)
      , fn () => genLet (e, TyStr, d)
      (* ---- DIMENSION-SPECIFIC: render datatype shape as a string (tag dispatch) ---- *)
      , fn () => "(case " ^ gen (e, TyOpt, d-1)
                 ^ " of Non => \"none\" | Som n => \"some:\" ^ Int.toString n)"
      , fn () => "(case " ^ gen (e, TyEither, d-1)
                 ^ " of Lft n => \"L\" ^ Int.toString n | Rgt s => \"R\" ^ s)"
      , fn () => "(treeShow " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => genHandle (e, TyStr, d)
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
      (* tree -> (sum, depth) via the recursive folds *)
      , fn () => "(let val t = " ^ gen (e, TyTree, d-1)
                 ^ " in (treeSum t, treeDepth t) end)"
      , fn () => genHandle (e, TyPair, d)
      ]
  in (pick prods) () end

(* ---- TyTree constructors + recursion.  BUILD depth is bounded by d, so the
        constructed tree is small.  A Br has two recursive subtrees. ---- *)
and genTree (e, d) : string =
  let
    val prods =
      [ fn () => "(Leaf " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Br (" ^ gen (e, TyTree, d-1) ^ ", " ^ gen (e, TyTree, d-1) ^ "))"
      (* map over the tree's leaves (recursive transformer) *)
      , fn () => "(treeMap (fn x => " ^ genIntInX (e, d-1) ^ ") "
                 ^ gen (e, TyTree, d-1) ^ ")"
      (* build a balanced-ish tree from a list (recursive constructor) *)
      , fn () => "(listToTree " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => genIf (e, TyTree, d)
      , fn () => genLet (e, TyTree, d)
      , fn () => genHandle (e, TyTree, d)
      ]
  in (pick prods) () end

and genOpt (e, d) : string =
  let
    val prods =
      [ fn () => "Non"
      , fn () => "(Som " ^ gen (e, TyInt, d-1) ^ ")"
      (* map over an option *)
      , fn () => "(case " ^ gen (e, TyOpt, d-1)
                 ^ " of Non => Non | Som n => Som (n + 1))"
      (* find first leaf > 0 in a tree -> option (recursive search) *)
      , fn () => "(treeFind " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => genIf (e, TyOpt, d)
      , fn () => genLet (e, TyOpt, d)
      , fn () => genHandle (e, TyOpt, d)
      ]
  in (pick prods) () end

and genEither (e, d) : string =
  let
    val prods =
      [ fn () => "(Lft " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Rgt " ^ gen (e, TyStr, d-1) ^ ")"
      (* classify an int: even -> Lft, odd -> Rgt of its string *)
      , fn () => "(let val n = " ^ gen (e, TyInt, d-1)
                 ^ " in if n mod 2 = 0 then Lft n else Rgt (Int.toString n) end)"
      , fn () => genIf (e, TyEither, d)
      , fn () => genLet (e, TyEither, d)
      , fn () => genHandle (e, TyEither, d)
      ]
  in (pick prods) () end

and genIntInX (e, d) : string =
  gen (("x", TyInt) :: e, TyInt, Int.max (1, d))

and genIntInI (e, d) : string =
  gen (("i", TyInt) :: e, TyInt, Int.max (1, d));

(* ===================================================================== *)
(* 5. The per-program preamble: user datatypes, exceptions, and the FIXED  *)
(*    recursive helper functions over them (all FUEL-free here because the  *)
(*    GENERATED trees are bounded in BUILD depth -- the structure itself is  *)
(*    finite and small, so a structural recursion terminates).             *)
(*                                                                          *)
(*    The helpers RAISE user exceptions on specific data shapes (e.g.       *)
(*    treeProd raises E1 on a zero leaf, then catches it to short-circuit)  *)
(*    so exn flow runs THROUGH the recursive descent.                       *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog_dre.sml -- DO NOT EDIT *)\n" ^
  (* ---- user datatypes ---- *)
  "datatype itree = Leaf of int | Br of itree * itree;\n" ^
  "datatype ibox = Non | Som of int;\n" ^
  "datatype ieither = Lft of int | Rgt of string;\n" ^
  (* ---- user exceptions: E1 carries an int, E2 is nullary ---- *)
  "exception E1 of int;\n" ^
  "exception E2;\n" ^
  (* ---- wrap: an escaped exception becomes a comparable token.  USR catches
          our own user exns explicitly (so an uncaught E1/E2 is comparable as a
          distinct token, not lumped into the generic _).  ---- *)
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\"\n" ^
  "  | E1 _ => \"USR1\" | E2 => \"USR2\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n" ^
  (* ---- recursive folds over itree ---- *)
  "fun treeSum (Leaf n) = n\n" ^
  "  | treeSum (Br (l, r)) = treeSum l + treeSum r;\n" ^
  "fun treeDepth (Leaf _) = 1\n" ^
  "  | treeDepth (Br (l, r)) = 1 + Int.max (treeDepth l, treeDepth r);\n" ^
  (* treeProd: short-circuit product -- raise E1 0 on a zero leaf, catch at the
     top so the whole product is 0 without descending the rest.  Exn flow
     THROUGH the recursive descent + a catch several frames up. *)
  "fun treeProdAux (Leaf 0) = raise E1 0\n" ^
  "  | treeProdAux (Leaf n) = n\n" ^
  "  | treeProdAux (Br (l, r)) = treeProdAux l * treeProdAux r;\n" ^
  "fun treeProd t = (treeProdAux t) handle E1 _ => 0;\n" ^
  (* treeAny: any leaf strictly positive? recursive predicate *)
  "fun treeAny (Leaf n) = n > 0\n" ^
  "  | treeAny (Br (l, r)) = treeAny l orelse treeAny r;\n" ^
  (* in-order flatten *)
  "fun treeFlat (Leaf n) = [n]\n" ^
  "  | treeFlat (Br (l, r)) = treeFlat l @ treeFlat r;\n" ^
  (* recursive leaf-map *)
  "fun treeMap f (Leaf n) = Leaf (f n)\n" ^
  "  | treeMap f (Br (l, r)) = Br (treeMap f l, treeMap f r);\n" ^
  (* render shape+values to a string (tag dispatch + recursion) *)
  "fun treeShow (Leaf n) = \"L\" ^ Int.toString n\n" ^
  "  | treeShow (Br (l, r)) = \"(\" ^ treeShow l ^ \"+\" ^ treeShow r ^ \")\";\n" ^
  (* find first (in-order) leaf > 0, raising/catching to short-circuit ->
     ibox option.  Another exn-through-recursion path. *)
  "fun treeFindAux (Leaf n) = if n > 0 then raise E1 n else ()\n" ^
  "  | treeFindAux (Br (l, r)) = (treeFindAux l; treeFindAux r);\n" ^
  "fun treeFind t = ((treeFindAux t; Non) handle E1 k => Som k);\n" ^
  (* build a balanced tree from a list; [] -> a single Leaf 0 sentinel; a
     genuine recursive constructor (split list in half). NOTE: only ever called
     on the bounded litIntList/derived lists, so it terminates fast. *)
  "fun listToTree [] = Leaf 0\n" ^
  "  | listToTree [x] = Leaf x\n" ^
  "  | listToTree xs =\n" ^
  "      let val n = List.length xs\n" ^
  "          val h = n div 2\n" ^
  "          fun take (0, _) = [] | take (_, []) = [] | take (k, y::ys) = y :: take (k-1, ys)\n" ^
  "          fun drop (0, ys) = ys | drop (_, []) = [] | drop (k, _::ys) = drop (k-1, ys)\n" ^
  "      in Br (listToTree (take (h, xs)), listToTree (drop (h, xs))) end;\n";

fun resultToString (TyInt, body)     = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)    = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body) = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)     = "wrap (fn () => (" ^ body ^ "))"
  | resultToString (TyPair, body)    = "wrap (fn () => pr2s (" ^ body ^ "))"
  (* datatypes are folded to a string for printing (deterministic, comparable) *)
  | resultToString (TyTree, body)    = "wrap (fn () => treeShow (" ^ body ^ "))"
  | resultToString (TyOpt, body)     =
      "wrap (fn () => (case (" ^ body ^ ") of Non => \"none\" | Som n => \"some:\" ^ Int.toString n))"
  | resultToString (TyEither, body)  =
      "wrap (fn () => (case (" ^ body ^ ") of Lft n => \"L\" ^ Int.toString n | Rgt s => \"R\" ^ s))";

(* the per-program BODY (one printing decl), WITHOUT the shared preamble. *)
fun programBody (i : int) : string =
  let
    val () = vctr := 0
    val rt = pick allTys
    val body = gen ([], rt, cfgDepth)
    val label = cfgPrefix ^ Int.toString i
    val rs = resultToString (rt, body)
  in
    "val () = print (\"@@" ^ label ^ "=\" ^ (" ^ rs ^ ") ^ \"\\n\");\n"
  end;

(* a standalone program file = preamble + one body. *)
fun program (i : int) : string = preamble ^ programBody i;

(* ===================================================================== *)
(* 6. Emit N program files into cfgOut                                     *)
(* ===================================================================== *)
fun ensureDir d =
  if OS.FileSys.access (d, []) then ()
  else OS.FileSys.mkDir d;

fun writeFile (path, contents) =
  let val os = TextIO.openOut path
  in TextIO.output (os, contents); TextIO.closeOut os end;

val cfgBundle = (case OS.Process.getEnv "GENPROG_BUNDLE" of
                     SOME "1" => true | SOME "true" => true | _ => false);

(* unbundled: one self-contained file per program (PREFIX<i>.sml). *)
fun emitFiles () =
  let
    val () = ensureDir cfgOut
    fun loop i =
      if i >= cfgN then ()
      else
        let val path = cfgOut ^ "/" ^ cfgPrefix ^ Int.toString i ^ ".sml"
        in writeFile (path, program i); loop (i + 1) end
  in
    loop 0;
    print ("genprog_dre: wrote " ^ Int.toString cfgN ^ " program FILE(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

(* bundled: ONE file (PREFIX.sml) = the shared preamble ONCE, then N program
   bodies appended.  Each body is independent top-level decls printing one @@
   line; bundling is sound (verified byte-identical to the per-file outputs) and
   lets CI run ONE poly invocation instead of N. *)
fun emitBundle () =
  let
    val () = ensureDir cfgOut
    fun bodies i acc = if i >= cfgN then acc else bodies (i + 1) (acc ^ programBody i)
    val src = preamble ^ bodies 0 ""
    val path = cfgOut ^ "/" ^ cfgPrefix ^ ".sml"
  in
    writeFile (path, src);
    print ("genprog_dre: wrote 1 BUNDLE (" ^ Int.toString cfgN ^ " programs) to " ^ path
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = if cfgBundle then emitBundle () else emitFiles ();
