(* diff-corpus category: closures — currying, captured refs, fn-returning-fn, memoization, fixpoint *)

(* 1. Curried fn partially applied and stored in a list; force each later. *)
val () =
  let
    fun adder a b c = a + b * 100 + c * 10000
    val partials = [adder 1, adder 2, adder 3]           (* each captures a *)
    val mids = map (fn f => f 5) partials                (* now b=5 *)
    val finals = List.concat (map (fn g => [g 7, g 9]) mids)
    val total = foldl (op +) 0 finals
  in
    print ("@@curry_partial_store=" ^ Int.toString total ^ "\n")
  end;

(* 2. Closure capturing a mutable ref used as a stateful counter/generator. *)
val () =
  let
    fun makeCounter init =
      let val r = ref init
      in (fn () => (r := !r + 1; !r), fn () => !r) end
    val (next, peek) = makeCounter 100
    val a = next ()
    val b = next ()
    val c = next ()
    val p = peek ()
    val (next2, _) = makeCounter 0   (* independent state *)
    val d = next2 ()
  in
    print ("@@counter_closure_state=" ^ Int.toString (a + b * 7 + c * 13 + p * 17 + d * 19) ^ "\n")
  end;

(* 3. Closures capturing loop variable — classic capture-by-value semantics. *)
val () =
  let
    val fns = List.tabulate (10, fn i => (fn x => x * i + i))
    val applied = map (fn f => f 3) fns
    val total = foldl (op +) 0 applied
  in
    print ("@@loop_var_capture=" ^ Int.toString total ^ "\n")
  end;

(* 4. Function-returning-function chains: deep currying with mixed capture. *)
val () =
  let
    fun chain a = fn b => fn c => fn d => fn e =>
      ((a - b) * c + d) mod (e + 1)
    val step = chain 1000
    val partial1 = step 17
    val partial2 = partial1 5
    val results =
      [ partial2 3 100
      , partial2 8 200
      , (chain 50 10 2 4 9)
      , ((((chain 7 2) 3) 11) 4) ]
    val total = foldl (op +) 0 results
  in
    print ("@@fn_returning_fn_chain=" ^ Int.toString total ^ "\n")
  end;

(* 5. Fold that BUILDS a closure (function composition accumulator). *)
val () =
  let
    val steps = [fn x => x + 3, fn x => x * 2, fn x => x - 5, fn x => x * x mod 1000]
    val composed = foldl (fn (f, acc) => fn x => f (acc x)) (fn x => x) steps
    val r1 = composed 4
    val r2 = composed 10
    val r3 = composed ~2
  in
    print ("@@fold_build_closure=" ^ Int.toString (r1 + r2 * 31 + r3 * 7) ^ "\n")
  end;

(* 6. Memoization via a ref-array (mutable cache captured in closure). *)
val () =
  let
    val cache = Array.array (40, ~1)
    fun fib n =
      if n < 2 then n
      else
        let val cached = Array.sub (cache, n)
        in if cached >= 0 then cached
           else let val v = fib (n - 1) + fib (n - 2)
                in Array.update (cache, n, v); v end
        end
    val results = List.tabulate (15, fn i => fib (i * 2))
    val total = foldl (op +) 0 results
  in
    print ("@@memo_ref_array_fib=" ^ Int.toString total ^ "\n")
  end;

(* 7. Y-combinator-ish fixpoint via a ref cell holding the recursive fn. *)
val () =
  let
    val self : (int -> int) ref = ref (fn _ => 0)
    val () = self := (fn n => if n <= 1 then 1 else n * (!self) (n - 1))
    val fact = !self
    val results = map fact [0, 1, 5, 8, 10]
    val total = foldl (op +) 0 results
  in
    print ("@@fixpoint_via_ref=" ^ Int.toString total ^ "\n")
  end;

(* 8. Closures over a datatype-carried environment; big case dispatch. *)
val () =
  let
    datatype expr = Const of int | Var | Add of expr * expr | Mul of expr * expr | Neg of expr
    fun compile (Const k) = (fn _ => k)
      | compile Var       = (fn x => x)
      | compile (Add (a, b)) = let val fa = compile a and fb = compile b in fn x => fa x + fb x end
      | compile (Mul (a, b)) = let val fa = compile a and fb = compile b in fn x => fa x * fb x end
      | compile (Neg a)      = let val fa = compile a in fn x => ~(fa x) end
    val e = Add (Mul (Var, Var), Neg (Add (Const 7, Mul (Const 2, Var))))
    val f = compile e
    val pts = map f [0, 1, 2, 3, 4, 5, ~3]
    val total = foldl (op +) 0 pts
  in
    print ("@@closure_compiled_expr=" ^ Int.toString total ^ "\n")
  end;

(* 9. Mutually-recursive closures sharing captured refs (state machine). *)
val () =
  let
    val log = ref ([] : int list)
    fun push x = log := x :: !log
    fun even 0 = (push 0; true)
      | even n = (push n; odd (n - 1))
    and odd 0 = (push ~1; false)
      | odd n = (push (~n); even (n - 1))
    val r1 = even 6
    val r2 = odd 5
    val sumLog = foldl (op +) 0 (!log)
    val tagged = (if r1 then 1 else 0) + (if r2 then 100 else 0)
  in
    print ("@@mutual_closure_state=" ^ Int.toString (sumLog * 1000 + tagged) ^ "\n")
  end;

(* 10. The IntInf.andb-shape: isShort-guarded branch, closures over operands.
   This is the exact bug shape: (small,big) must take the rts path, not truncate. *)
val () =
  let
    fun mkAnd (i, j) =
      fn () =>
        if RunCall.isShort i andalso RunCall.isShort j
        then IntInf.andb (i, j)     (* both-short path *)
        else IntInf.andb (i, j)     (* general path — (small,big) MUST land here *)
    val big = IntInf.pow (2, 80) + 255
    val ops = [ mkAnd (255, 240)        (* both short *)
              , mkAnd (240, big)        (* small,big — the andb-truncation shape *)
              , mkAnd (big, 240)        (* big,small *)
              , mkAnd (big, big) ]      (* big,big *)
    val results = map (fn f => IntInf.toString (f ())) ops
  in
    print ("@@isshort_guard_andb=" ^ String.concatWith "," results ^ "\n")
  end;

(* 11. Closure escaping its defining scope, capturing a local that is shadowed. *)
val () =
  let
    fun make () =
      let
        val x = 11
        val g = fn y => x * y
        val x = 999                 (* shadows; g must still see 11 *)
        val h = fn y => x + y
      in (g, h) end
    val (g, h) = make ()
    val results = [g 4, h 4, g 0, h 0]
    val total = foldl (op +) 0 results
  in
    print ("@@closure_shadow_capture=" ^ Int.toString total ^ "\n")
  end;

(* 12. Higher-order pipeline: produce closures, store in array, replay in order. *)
val () =
  let
    val ops = Array.array (5, fn (x:int) => x)
    val () = Array.update (ops, 0, fn x => x + 1)
    val () = Array.update (ops, 1, fn x => x * 3)
    val () = Array.update (ops, 2, fn x => x - 2)
    val () = Array.update (ops, 3, fn x => x * x)
    val () = Array.update (ops, 4, fn x => x mod 97)
    fun run acc i = if i >= 5 then acc else run (Array.sub (ops, i) acc) (i + 1)
    val results = map (run 5) [0, 0, 0]   (* run all from seed 5, then... *)
    (* actually replay starting seed varies: *)
    val seeds = [2, 7, 13, 100]
    val outs = map (fn s => run s 0) seeds
    val total = foldl (op +) 0 outs + foldl (op +) 0 results
  in
    print ("@@closure_array_pipeline=" ^ Int.toString total ^ "\n")
  end;

(* 13. Closure capturing accumulator across a continuation-passing recursion. *)
val () =
  let
    fun sumcps [] k = k 0
      | sumcps (x :: xs) k = sumcps xs (fn acc => k (x + acc))
    fun prodcps [] k = k 1
      | prodcps (x :: xs) k = prodcps xs (fn acc => k (x * acc))
    val lst = [1, 2, 3, 4, 5, 6]
    val s = sumcps lst (fn r => r)
    val p = prodcps lst (fn r => r)
    val combined = sumcps lst (fn sv => prodcps lst (fn pv => sv * 10000 + pv))
  in
    print ("@@cps_closure_accum=" ^ Int.toString (s + p + combined) ^ "\n")
  end;

(* 14. Generator closures producing a stream; capture iterator state in ref. *)
val () =
  let
    fun makeGen start step =
      let val r = ref start
      in fn () => let val v = !r in r := !r + step; v end end
    val g1 = makeGen 0 2
    val g2 = makeGen 1 3
    fun take g 0 acc = List.rev acc
      | take g n acc = take g (n - 1) (g () :: acc)
    val s1 = take g1 6 []
    val s2 = take g2 6 []
    val zipped = ListPair.map (fn (a, b) => a * b) (s1, s2)
    val total = foldl (op +) 0 zipped
  in
    print ("@@generator_closure_stream=" ^ Int.toString total ^ "\n")
  end;

(* 15. Closure capturing a real ref-accumulator; deterministic Real output. *)
val () =
  let
    fun makeAvg () =
      let val sum = ref 0.0 and cnt = ref 0
      in fn x => (sum := !sum + x; cnt := !cnt + 1; !sum / Real.fromInt (!cnt)) end
    val avg = makeAvg ()
    val last = foldl (fn (x, _) => avg x) 0.0 [2.0, 4.0, 6.0, 8.0, 10.0]
  in
    print ("@@closure_real_running_avg=" ^ Real.fmt (StringCvt.FIX (SOME 8)) last ^ "\n")
  end;

(* 16. Exception escaping a closure boundary; handler restores via closure. *)
val () =
  let
    exception Stop of int
    fun guarded f x = (f x; ~1) handle Stop k => k
    val threshold = 50
    fun accumUntil lst =
      let val acc = ref 0
      in
        guarded
          (fn () => app (fn x => (acc := !acc + x; if !acc > threshold then raise Stop (!acc) else ())) lst)
          ()
      end
    val r1 = accumUntil [10, 20, 30, 40]
    val r2 = accumUntil [1, 2, 3]            (* never exceeds; returns ~1 *)
  in
    print ("@@closure_exception_escape=" ^ Int.toString (r1 * 1000 + r2) ^ "\n")
  end;
