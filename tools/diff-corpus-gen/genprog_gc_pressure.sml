(* genprog_gc_pressure.sml -- TYPE-DIRECTED random SML PROGRAM generator.
   DIMENSION = gc_pressure: allocation-HEAVY whole programs that build LARGE
   (bounded) lists / tuples / refs / user datatype values, fold over them,
   create + discard MANY intermediate structures, and use deep-ish recursion --
   so that MANY copying-GC cycles fire WITHIN the harness max-steps budget. A GC
   bug (heap corruption, mis-forwarded pointer, wrong Cheney copy) then shows up
   as a WRONG RESULT or a crash, caught differentially against upstream.
   ==========================================================================
   This is a SEAT of the shared genprog framework (tools/diff-corpus-gen/
   genprog.sml). It keeps the framework invariants UNCHANGED -- the same LCG
   (seeded from GENPROG_SEED), the same wrap-exn-to-token discipline, the same
   deterministic stringify, the same ASCII-clean output -- and ADDS the typed
   productions / new ty constructors that exercise the gc_pressure dimension.

   WHY the gc_pressure seat: GC correctness (Cheney copy + from-space pointer
   fixup) only manifests when a collection happens DURING a live computation --
   per-op and per-program fuzzers rarely allocate enough to trip even one
   cycle, much less many. This seat deliberately drives allocation HARD:
     - List.tabulate up to ~LARGE elements, then fold to a single int/checksum.
     - "alloc storms": build N intermediate lists/tuples/datatype values in a
       loop, keep a rolling checksum, discard the rest (so the live set churns
       and the GC must copy + fix up pointers repeatedly).
     - a `ref`-cell loop: allocate refs, write, read them back, sum (mutable
       cells across a collection exercise the write barrier / ref fixup).
     - a recursively-built BINARY TREE (a user datatype) of bounded depth, then
       fold/sum it (datatype rep + deep pointer chains the GC must walk).
     - deep-ish recursion (bounded fuel) so the stack itself is live across GC.
   Every program REDUCES to a SMALL deterministic value (an int / bool /
   short string), so output stays tiny + comparable while the COMPUTE is heavy.

   The genuinely new coverage over the existing cstress_heavy.sml (hand-written,
   fixed constants) is the COMBINATION + variation: the allocation sizes, tree
   depths, fold operators, and the control flow threading them are all
   LCG-varied and type-directed -- a closure folding a tabulate'd list whose
   element fn allocates a sub-list, inside an if, inside a let -- combinations a
   fixed corpus never reaches, each guaranteed well-typed and terminating.

   SOUNDNESS (identical to the base framework):
   1. TYPE-DIRECTED => well-typed BY CONSTRUCTION. Every production emits an
      expression of exactly the requested type; every lambda binds its argument
      into the env before generating its (typed) body.
   2. DETERMINISTIC LCG; reproducible per seed.
   3. EVERY result wrapped: exn -> comparable token. Both sides raising the same
      exn => agree.
   4. BOUNDED: depth, list lengths, tabulate counts, alloc-loop counts, tree
      depth, recursion fuel ALL capped. Programs terminate in well under the
      harness max-steps; the caps are tuned so the GC fires (tens of MB of
      churn) but the program still finishes in << 1s.
   5. TOTALLY STRINGIFIED + DETERMINISTIC: int / bool / int list / string /
      (int*int) results only. NO Real fmt, NO ref/exn/fn printing, NO andb/orb
      on big IntInf. (Refs are READ BACK to ints, never printed by identity.)

   GC-CADENCE NOTE: our copying GC fires at ~80% of the alloc cap (see
   CLAUDE.md). The /tmp/basis_loaded default heap is large, so to FORCE many
   cycles within max-steps we need genuine churn. The alloc-loop + big-tabulate
   productions allocate hundreds of thousands of words of garbage per program,
   which over a depth-5/6 program (several such productions composed) is enough
   to trip the collector. We do NOT rely on a single giant allocation (which a
   big heap could absorb without collecting) -- we rely on REPEATED allocation
   inside loops so the from-space churns and the copy/fixup path runs.

   USAGE (run on the trusted UPSTREAM poly):
     GENPROG_SEED=42 GENPROG_N=400 GENPROG_OUT=tools/diff-corpus-gen/out/gc_pressure \
       GENPROG_PREFIX=genprog_gc_pressure_ /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_gc_pressure.sml
   Then:
     tools/diff-oracle.sh --dir tools/diff-corpus-gen/out/gc_pressure
     POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir tools/diff-corpus-gen/out/gc_pressure
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
val cfgOut    = getStr ("GENPROG_OUT", "/tmp/genprog_gc_pressure");
val cfgDepth  = getInt ("GENPROG_DEPTH", 5);
val cfgPrefix = getStr ("GENPROG_PREFIX", "gc");
(* GENPROG_BUNDLE=<path>: when set, emit ONE self-contained .sml file at <path>
   with a single shared preamble + N labelled print lines (the existing
   fuzz_*.sml / genprog_arith corpus idiom), instead of N separate per-program
   files in cfgOut. This amortizes our ~1.2s checkpoint-load startup across all
   N programs so the batch is cheap enough for CI. Each program body is a single
   EXPRESSION (no top-level decls), so concatenating them under one preamble is
   sound. *)
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
(*    Closed type set extended for the gc_pressure dimension:             *)
(*      TyTree = a generated user binary-tree datatype `gctree` (declared *)
(*               once in the program preamble). Values are CONSTRUCTED by  *)
(*               recursive builders and DECONSTRUCTED via `case`, so they  *)
(*               form deep heap pointer chains the GC must walk + copy.    *)
(* ===================================================================== *)
datatype ty = TyInt | TyBool | TyIntList | TyStr | TyPair | TyTree;

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
(* a leaf tree value: Lf <int>  (the program preamble declares the datatype) *)
fun litTree () = "(Lf " ^ litInt () ^ ")";

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
            | TyTree => litTree ())
  end;

(* ===================================================================== *)
(* 4. The type-directed core                                              *)
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

and genLet (e : env, t : ty, d : int) : string =
  let val bt = pick [TyInt, TyBool, TyIntList, TyStr, TyPair, TyTree]
      val x = freshVar ()
      val rhs = gen (e, bt, d - 1)
      val e' = (x, bt) :: e
      val body = gen (e', t, d - 1)
  in "(let val " ^ x ^ " = " ^ rhs ^ " in " ^ body ^ " end)" end

and genIf (e : env, t : ty, d : int) : string =
  "(if " ^ gen (e, TyBool, d - 1) ^ " then " ^ gen (e, t, d - 1)
  ^ " else " ^ gen (e, t, d - 1) ^ ")"

(* ----------------------------------------------------------------- *)
(* COST DISCIPLINE for the heavy productions.                          *)
(* The allocation-heavy productions (big tabulate / alloc-storm /      *)
(* ref-loop / nested-tabulate / string-storm / tree-build) run a       *)
(* LOOP or per-element LAMBDA bounded-but-LARGE times. If the SIZE     *)
(* expression or the per-element BODY were a full recursive heavy      *)
(* production, the heavy compute would MULTIPLY (O(n) heavy bodies, or *)
(* heavy compute nested inside heavy compute) -> pathological runtimes *)
(* (observed: a depth-5 program nesting three of them ran ~34s).       *)
(*                                                                     *)
(* Fix: heavy productions take their COUNT from a CHEAP int (a small   *)
(* type-directed int at depth<=2 -- still varied, still well-typed,    *)
(* but it cannot itself be a heavy production), and their per-element   *)
(* lambda bodies are CHEAP ints too. The allocation MAGNITUDE is       *)
(* unchanged (still hundreds of thousands of words -> GC fires); only  *)
(* the per-element/per-iteration COMPUTE is kept O(1). The OUTER       *)
(* program structure (the heavy production sitting inside an if/let/    *)
(* case) still composes freely, so the dimension's combination         *)
(* coverage is preserved -- only the multiplicative blow-up is cut.    *)
(* ----------------------------------------------------------------- *)
(* genIntLight: a TYPE-DIRECTED int generator that emits ONLY O(1)-cost
   productions -- NO heavy allocation production (no big tabulate / alloc-storm /
   ref-loop / nested-tabulate / string-storm / tree-build). It is the generator
   used in EVERY HOT/CHEAP position: the SIZE counts of heavy productions and the
   per-element/per-iteration LAMBDA BODIES. This is what guarantees the
   heavy-allocation magnitude is bounded: a heavy production's count is a SMALL
   int (no nested heavy compute), and its element fn does O(1) work. Without this
   (the earlier `cheapInt` merely reduced DEPTH), a "cheap" position could still
   recurse into a heavy production at depth 2 -- which produced an alloc-storm as
   a tabulate ELEMENT fn => O(n*storm) = BILLIONS of allocations (the 4/400 cost
   blow-ups: gcp321/gcp370 etc). genIntLight CANNOT do that: heavy productions
   are simply absent from its list. Depth still bounds nesting of the light ops. *)
and genIntLight (e, d) : string =
  if d <= 0 then leaf (e, TyInt)
  else
    let
      val prods =
        [ fn () => "(" ^ genIntLight (e, d-1) ^ " + " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(" ^ genIntLight (e, d-1) ^ " - " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(" ^ genIntLight (e, d-1) ^ " * " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(Int.max (" ^ genIntLight (e, d-1) ^ ", " ^ genIntLight (e, d-1) ^ "))"
        , fn () => "(Int.min (" ^ genIntLight (e, d-1) ^ ", " ^ genIntLight (e, d-1) ^ "))"
        , fn () => "(~ " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(Int.abs " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(" ^ genIntLight (e, d-1) ^ " div " ^ genIntLight (e, d-1) ^ ")"
        , fn () => "(" ^ genIntLight (e, d-1) ^ " mod " ^ genIntLight (e, d-1) ^ ")"
        , fn () => leaf (e, TyInt)
        ]
    in (pick prods) () end

(* a SMALL bounded int for sizing a heavy production's count (depth<=2, light) *)
and cheapInt (e, d) = genIntLight (e, Int.min (2, Int.max (0, d - 1)))

(* a `fn x => <int-body mentioning x>` -- for map/tabulate element fns *)
and lamIntToInt (e, d) =
  "(fn x => " ^ gen (("x", TyInt) :: e, TyInt, Int.max (1, d)) ^ ")"
and lamIntToBool (e, d) =
  "(fn x => " ^ gen (("x", TyInt) :: e, TyBool, Int.max (1, d)) ^ ")"
(* tabulate index fn: int -> int mentioning i *)
and lamTabInt (e, d) =
  "(fn i => " ^ gen (("i", TyInt) :: e, TyInt, Int.max (1, d)) ^ ")"
(* CHEAP (LIGHT-ONLY) per-element fns for HEAVY productions: the body is a
   genIntLight, so it CANNOT itself be a heavy allocation -- the per-element cost
   stays O(1) and the heavy production's total allocation stays O(n). Still uses
   i/x as a leaf so the closure genuinely captures/depends on the index. *)
and lamTabIntCheap (e, d) =
  "(fn i => " ^ genIntLight (("i", TyInt) :: e, Int.min (2, Int.max (1, d - 1))) ^ ")"
and lamIntToIntCheap (e, d) =
  "(fn x => " ^ genIntLight (("x", TyInt) :: e, Int.min (2, Int.max (1, d - 1))) ^ ")"
(* a `fn (a,b) => <int>` folder: a = element, b = accumulator (both int) *)
and lamFoldInt (e, d) =
  let val acc = freshVar ()
      val e' = (acc, TyInt) :: ("x", TyInt) :: e
  in "(fn (x, " ^ acc ^ ") => " ^ gen (e', TyInt, Int.max (1, d)) ^ ")" end

(* ----------------------------------------------------------------- *)
(* INT productions: the gc_pressure CORE -- big allocation reduced to *)
(* a single int. Sizes are bounded so the program terminates fast but *)
(* allocates enough to churn the heap and trip the copying GC.         *)
(*                                                                     *)
(* Bounded sizing convention:  N  =  Int.abs(<gen int>) mod CAP + BASE *)
(* so every count is in [BASE, BASE+CAP).  We keep counts in the low   *)
(* thousands per production; a depth-5 program composes several of them *)
(* -> hundreds of thousands of allocated words -> the GC fires.        *)
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
      , fn () => "(List.length " ^ gen (e, TyIntList, d-1) ^ ")"

      (* === GC-PRESSURE int reductions (the heart of this seat) === *)

      (* (A) big tabulate -> foldl sum. Count in [2000, 5999]. Builds a fresh
            cons-chain of up to ~6000 cells, folds it to a single int. The
            element fn is a CHEAP closure (may capture outer vars; O(1) body). *)
      , fn () => "(let val n = Int.abs (" ^ cheapInt (e, d) ^ ") mod 4000 + 2000"
                 ^ " in List.foldl (fn (a,b) => a + b) 0 (List.tabulate (n, "
                 ^ lamTabIntCheap (e, d) ^ ")) end)"

      (* (B) ALLOC STORM: a fuel'd loop that on each iteration builds a fresh
            intermediate list (List.tabulate sz), reduces it, adds to a rolling
            accumulator, and DISCARDS the list. Iterations * sz = lots of churn
            -> repeated from-space allocation -> the GC must copy + fixup the
            live acc across each collection. iters in [3000,6999], sz in
            [50,149]. Total allocation ~ up to 7000*150 ~= 1M cells, all garbage
            but acc -- enough to trip several copying-GC cycles on a moderate
            heap. The per-iteration body is O(sz) but allocation-bound, so the
            program still finishes fast. *)
      , fn () => "(let fun loop k acc = if k <= 0 then acc"
                 ^ " else loop (k-1) (acc + List.foldl (fn (a,b) => a+b) 0"
                 ^ " (List.tabulate (k mod 100 + 50, fn j => j + k)))"
                 ^ " in loop (Int.abs (" ^ cheapInt (e, d) ^ ") mod 4000 + 3000) 0 end)"

      (* (C) REF-CELL loop: allocate a list of refs, write to each, read back,
            sum. Exercises the mutable-cell allocation + read-after-GC path.
            Count in [500,1499]. We build the refs, force them live in a list,
            then fold the dereferences. *)
      , fn () => "(let val n = Int.abs (" ^ cheapInt (e, d) ^ ") mod 1000 + 500"
                 ^ " val rs = List.tabulate (n, fn i => ref (i * 3))"
                 ^ " val () = List.app (fn r => r := !r + 1) rs"
                 ^ " in List.foldl (fn (r,acc) => acc + !r) 0 rs end)"

      (* (D) TREE BUILD + SUM: build a balanced binary tree of bounded depth
            (a user datatype `gctree`), then sum its leaves. depth in [8,13]
            -> up to 2^13 = 8192 nodes, a deep pointer chain the GC walks. *)
      , fn () => "(let val dpth = Int.abs (" ^ cheapInt (e, d) ^ ") mod 6 + 8"
                 ^ " in sumTree (buildTree dpth) end)"

      (* (E) NESTED tabulate: a list of lists (tabulate of tabulate), summed.
            outer in [40,139], inner in [40,139] -> up to ~19k cells churned. *)
      , fn () => "(let val n = Int.abs (" ^ cheapInt (e, d) ^ ") mod 100 + 40"
                 ^ " in List.foldl (fn (xs,acc) => acc + List.length xs) 0"
                 ^ " (List.tabulate (n, fn i => List.tabulate (n, fn j => i+j))) end)"

      (* (F) string-build storm reduced to size: concat many small strings then
            take the size. String allocation churns the byte-heap. iters
            [300,799]. (Kept smaller than the list storm: each ^ reallocates the
            WHOLE accumulator, so this is O(iters^2) bytes -- already heavy GC.) *)
      , fn () => "(let fun loop k acc = if k <= 0 then String.size acc"
                 ^ " else loop (k-1) (acc ^ Int.toString (k mod 100))"
                 ^ " in loop (Int.abs (" ^ cheapInt (e, d) ^ ") mod 500 + 300) \"\" end)"

      (* (G) LIVE-SET RETENTION UNDER CHURN -- the highest-value GC probe.
            Build a moderate LIVE list `keep` (5000-8999 cells), then run a heavy
            alloc storm (garbage tabulates) WHILE `keep` stays referenced, then
            FOLD `keep` at the end. The collector must COPY the live `keep` list
            across each collection and CORRECTLY FORWARD every pointer; a
            mis-forwarded pointer (the classic Cheney bug) corrupts the final
            fold => a wrong checksum the differential catches. (The 0%-retained
            garbage storms only exercise the trigger; THIS exercises the
            copy-of-LIVE-data + pointer-fixup path where forwarding bugs hide.)
            The expected value is deterministic: sum(0..|keep|-1) since the storm
            result is discarded. churn iters in [40000,79999] (cheap per-iter, but
            ~10M+ allocated words total -> several copying-GC cycles on a moderate
            heap, each of which must COPY+FORWARD the live `keep` correctly). *)
      , fn () => "(let val keep = List.tabulate (Int.abs (" ^ cheapInt (e, d)
                 ^ ") mod 4000 + 5000, fn i => i)"
                 ^ " fun churn k = if k <= 0 then 0"
                 ^ " else (List.foldl (fn (a,b) => a+b) 0 (List.tabulate (k mod 100 + 50, fn j => j+k));"
                 ^ " churn (k-1))"
                 ^ " val _ = churn (Int.abs (" ^ cheapInt (e, d) ^ ") mod 40000 + 40000)"
                 ^ " in List.foldl (fn (a,b) => a + b) 0 keep end)"

      (* (H) LIVE TREE retained across churn -- same idea, datatype edition. Build
            a balanced tree (live), churn garbage, then sum the LIVE tree. A
            forwarding bug on the tree's interior nodes corrupts the sum. depth
            [10,13] -> up to 8192 live nodes; churn iters [40000,79999]. *)
      , fn () => "(let val t = buildTree (Int.abs (" ^ cheapInt (e, d) ^ ") mod 4 + 10)"
                 ^ " fun churn k = if k <= 0 then 0"
                 ^ " else (List.tabulate (k mod 100 + 50, fn j => j+k); churn (k-1))"
                 ^ " val _ = churn (Int.abs (" ^ cheapInt (e, d) ^ ") mod 40000 + 40000)"
                 ^ " in sumTree t end)"

      (* ordinary reductions (keep the type space rich) *)
      , fn () => "(List.foldl " ^ lamFoldInt (e, d-1) ^ " " ^ gen (e, TyInt, d-1)
                 ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(String.size " ^ gen (e, TyStr, d-1) ^ ")"
      , fn () => "(#1 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(#2 " ^ gen (e, TyPair, d-1) ^ ")"
      , fn () => "(sumTree " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => "(depthTree " ^ gen (e, TyTree, d-1) ^ ")"
      (* fuel'd recursive accumulator sum *)
      , fn () => "(let fun f n acc = if n <= 0 then acc else f (n-1) (acc+n) in f ("
                 ^ "Int.abs (" ^ gen (e, TyInt, d-1) ^ ") mod 1000) 0 end)"
      , fn () => genIf (e, TyInt, d)
      , fn () => genLet (e, TyInt, d)
      (* multi-arm list pattern match *)
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => 0 | [a] => a | (a :: b :: _) => a + b)"
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
      (* structural equality on big lists -- the GC + structural-= combination:
         build two equal big tabulates and compare. *)
      , fn () => "(let val n = Int.abs (" ^ cheapInt (e, d) ^ ") mod 2000 + 500"
                 ^ " in List.tabulate (n, fn i => i mod 7) = List.tabulate (n, fn i => i mod 7) end)"
      , fn () => "(List.exists " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.all " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
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
      , fn () => "(List.map " ^ lamIntToInt (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      , fn () => "(List.filter " ^ lamIntToBool (e, d-1) ^ " " ^ gen (e, TyIntList, d-1) ^ ")"
      (* a bounded-but-LARGE tabulate that survives into the result list. We then
         REDUCE it back to a small list (take a few) so the printed value stays
         tiny -- the allocation churn is what matters. count in [1000,2999].
         CHEAP size + element fn (see COST DISCIPLINE). *)
      , fn () => "(List.take (List.rev (List.tabulate (Int.abs ("
                 ^ cheapInt (e, d) ^ ") mod 2000 + 1000, " ^ lamTabIntCheap (e, d)
                 ^ ")), 5))"
      (* map over a big tabulate then take the head few *)
      , fn () => "(List.take (List.map " ^ lamIntToIntCheap (e, d)
                 ^ " (List.tabulate (Int.abs (" ^ cheapInt (e, d)
                 ^ ") mod 1500 + 500, fn i => i)), 4))"
      (* small generated tabulate (bounded <=11) for variety *)
      , fn () => "(List.tabulate (Int.abs (" ^ gen (e, TyInt, d-1)
                 ^ ") mod 12, " ^ lamTabInt (e, d-1) ^ "))"
      (* flatten a tree to its leaf list, then take a few *)
      , fn () => "(List.take (treeLeaves " ^ gen (e, TyTree, d-1) ^ " @ [0,0,0,0,0], 5))"
      , fn () => "(case " ^ gen (e, TyIntList, d-1)
                 ^ " of [] => [] | (a :: rest) => rest @ [a])"
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
      (* a big concatWith over a big tabulate, then take a prefix -- string
         allocation churn reduced to a tiny printed prefix. count in [500,1499]. *)
      , fn () => "(String.substring (String.concatWith \"-\" (List.map Int.toString"
                 ^ " (List.tabulate (Int.abs (" ^ cheapInt (e, d)
                 ^ ") mod 1000 + 500, fn i => i mod 10))), 0, 9))"
      , fn () => genIf (e, TyStr, d)
      , fn () => genLet (e, TyStr, d)
      ]
  in (pick prods) () end

and genPair (e, d) : string =
  let
    val prods =
      [ fn () => "(" ^ gen (e, TyInt, d-1) ^ ", " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(let val p = " ^ gen (e, TyPair, d-1) ^ " in (#2 p, #1 p) end)"
      , fn () => "(let val (a, b) = " ^ gen (e, TyPair, d-1) ^ " in (b, a) end)"
      (* (length, sum) of a big tabulate -- pair-building over alloc churn.
         count in [1000,3999]. *)
      , fn () => "(let val xs = List.tabulate (Int.abs (" ^ cheapInt (e, d)
                 ^ ") mod 3000 + 1000, fn i => i mod 13)"
                 ^ " in (List.length xs, List.foldl (fn (a,b) => a + b) 0 xs) end)"
      , fn () => genIf (e, TyPair, d)
      , fn () => genLet (e, TyPair, d)
      ]
  in (pick prods) () end

(* ----------------------------------------------------------------- *)
(* TREE productions: construct the user `gctree` datatype. The big    *)
(* `buildTree` lives as a top-level helper (in the preamble); these   *)
(* productions assemble trees structurally so the GC walks the chain. *)
(* ----------------------------------------------------------------- *)
and genTree (e, d) : string =
  let
    val prods =
      [ fn () => "(Lf " ^ gen (e, TyInt, d-1) ^ ")"
      , fn () => "(Br (" ^ gen (e, TyTree, d-1) ^ ", " ^ gen (e, TyInt, d-1)
                 ^ ", " ^ gen (e, TyTree, d-1) ^ "))"
      (* a bounded balanced tree builder: depth in [6,11] -> up to 2^11 nodes *)
      , fn () => "(buildTree (Int.abs (" ^ cheapInt (e, d) ^ ") mod 6 + 6))"
      (* map an int fn over a tree's labels (rebuilds the whole tree).
         CHEAP element fn: a tree can have thousands of nodes, so an O(1) body
         keeps the rebuild linear (see COST DISCIPLINE). *)
      , fn () => "(mapTree " ^ lamIntToIntCheap (e, d) ^ " " ^ gen (e, TyTree, d-1) ^ ")"
      (* mirror a tree (rebuilds, swapping children) *)
      , fn () => "(mirrorTree " ^ gen (e, TyTree, d-1) ^ ")"
      , fn () => genIf (e, TyTree, d)
      , fn () => genLet (e, TyTree, d)
      ]
  in (pick prods) () end;

(* ===================================================================== *)
(* 5. The per-program wrapper + result stringifier                        *)
(*    The preamble declares the `gctree` datatype + its helpers so tree    *)
(*    productions have something to call. Helpers are bounded + total.     *)
(* ===================================================================== *)
val preamble =
  "(* generated by tools/diff-corpus-gen/genprog_gc_pressure.sml -- DO NOT EDIT *)\n" ^
  "datatype gctree = Lf of int | Br of gctree * int * gctree;\n" ^
  "fun buildTree d = if d <= 0 then Lf d else Br (buildTree (d-1), d, buildTree (d-1));\n" ^
  "fun sumTree (Lf n) = n | sumTree (Br (l, n, r)) = sumTree l + n + sumTree r;\n" ^
  "fun depthTree (Lf _) = 0 | depthTree (Br (l, _, r)) = 1 + Int.max (depthTree l, depthTree r);\n" ^
  "fun mapTree f (Lf n) = Lf (f n) | mapTree f (Br (l, n, r)) = Br (mapTree f l, f n, mapTree f r);\n" ^
  "fun mirrorTree (Lf n) = Lf n | mirrorTree (Br (l, n, r)) = Br (mirrorTree r, n, mirrorTree l);\n" ^
  "fun treeLeaves (Lf n) = [n] | treeLeaves (Br (l, _, r)) = treeLeaves l @ treeLeaves r;\n" ^
  "fun wrap f = (f ()) handle Overflow => \"OVF\" | Div => \"DIV\"\n" ^
  "  | Subscript => \"SUB\" | Size => \"SIZE\" | Empty => \"EMPTY\"\n" ^
  "  | Match => \"MATCH\" | Bind => \"BIND\" | _ => \"EXN\";\n" ^
  "fun il2s xs = \"[\" ^ String.concatWith \",\" (List.map Int.toString xs) ^ \"]\";\n" ^
  "fun pr2s (a,b) = \"(\" ^ Int.toString a ^ \",\" ^ Int.toString b ^ \")\";\n";

fun resultToString (TyInt, body)     = "wrap (fn () => Int.toString (" ^ body ^ "))"
  | resultToString (TyBool, body)    = "wrap (fn () => Bool.toString (" ^ body ^ "))"
  | resultToString (TyIntList, body) = "wrap (fn () => il2s (" ^ body ^ "))"
  | resultToString (TyStr, body)     = "wrap (fn () => (" ^ body ^ "))"
  | resultToString (TyPair, body)    = "wrap (fn () => pr2s (" ^ body ^ "))"
  (* a Tree result is reduced to its (sum, depth) pair so it is comparable *)
  | resultToString (TyTree, body)    =
      "wrap (fn () => let val t = (" ^ body ^ ") in pr2s (sumTree t, depthTree t) end)";

(* result types are biased toward INT (the dimension's allocation reductions all
   live in genInt) and TREE, so most programs end in a heavy-alloc reduction. *)
val resultTypes =
  [ TyInt, TyInt, TyInt, TyInt
  , TyTree, TyTree
  , TyPair
  , TyBool
  , TyIntList
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

fun program (i : int) : string = preamble ^ programLine i;

(* ===================================================================== *)
(* 6. Emit                                                                *)
(* ===================================================================== *)
fun ensureDir d =
  if OS.FileSys.access (d, []) then ()
  else OS.FileSys.mkDir d;

fun writeFile (path, contents) =
  let val os = TextIO.openOut path
  in TextIO.output (os, contents); TextIO.closeOut os end;

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
    print ("genprog_gc_pressure: wrote " ^ Int.toString cfgN ^ " file(s) to " ^ cfgOut
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

fun emitBundle () =
  let
    val hdr =
      "(* GENERATED by tools/diff-corpus-gen/genprog_gc_pressure.sml -- DO NOT EDIT.\n" ^
      "   gc_pressure dimension: type-directed whole-program differential fuzz\n" ^
      "   (allocation-heavy programs that force MANY copying-GC cycles, each\n" ^
      "   reduced to a small deterministic value).\n" ^
      "   Regenerate: GENPROG_SEED=" ^ Int.toString cfgSeed ^ " GENPROG_N=" ^ Int.toString cfgN ^
      " GENPROG_DEPTH=" ^ Int.toString cfgDepth ^ " GENPROG_PREFIX=" ^ cfgPrefix ^ "\n" ^
      "     GENPROG_BUNDLE=<path> /tmp/polybuild/poly < tools/diff-corpus-gen/genprog_gc_pressure.sml\n" ^
      "   " ^ Int.toString cfgN ^ " programs; each prints one labelled line of the\n" ^
      "   form (at)(at)" ^ cfgPrefix ^ "<i>=<wrapped result>. *)\n"
    fun loop (i, acc) = if i >= cfgN then acc else loop (i + 1, acc ^ programLine i)
    val body = loop (0, "")
  in
    writeFile (cfgBundle, hdr ^ preamble ^ body);
    print ("genprog_gc_pressure: wrote bundle of " ^ Int.toString cfgN ^ " program(s) to " ^ cfgBundle
           ^ " (seed=" ^ Int.toString cfgSeed ^ ", depth=" ^ Int.toString cfgDepth
           ^ ", prefix=" ^ cfgPrefix ^ ")\n")
  end;

val () = if cfgBundle <> "" then emitBundle () else emitFiles ();
