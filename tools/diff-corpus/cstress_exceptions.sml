(* 1: raise/handle inside a tight loop — count how many of 0..999 are caught
   when a div-by-zero-style exception is raised on multiples of 7. *)
local
  exception Skip
  fun classify n = if n mod 7 = 0 then raise Skip else n
  fun loop (i, acc) =
    if i >= 1000 then acc
    else
      let val contrib = (classify i handle Skip => 0)
      in loop (i + 1, acc + (if contrib = 0 then 1 else 0)) end
in
  val () = print ("@@tightloop_caught=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 2: exception carrying (int * string); handler pattern-matches the packet and
   reconstructs a checksum from the carried payload across several raises. *)
local
  exception Tag of int * string
  fun emit n =
    if n mod 3 = 0 then raise Tag (n, "fizz")
    else if n mod 5 = 0 then raise Tag (n, "buzz")
    else raise Tag (n, "num")
  fun score n =
    (emit n; 0)
    handle Tag (k, "fizz") => k + 1000
         | Tag (k, "buzz") => k + 2000
         | Tag (k, _)      => k
  fun loop (i, acc) = if i > 20 then acc else loop (i + 1, acc + score i)
in
  val () = print ("@@tagpacket_sum=" ^ Int.toString (loop (1, 0)) ^ "\n")
end

(* 3: re-raise — inner handler logs then re-raises; outer handler counts. *)
local
  exception Boom of int
  val log = ref 0
  fun inner n = (raise Boom n) handle Boom k => (log := !log + k; raise Boom (k * 2))
  fun outer n = (inner n) handle Boom k => k
  fun loop (i, acc) = if i > 10 then acc else loop (i + 1, acc + outer i)
in
  val tot = loop (1, 0)
  val () = print ("@@reraise=" ^ Int.toString (tot + !log) ^ "\n")
end

(* 4: nested handlers selecting by constructor; the optimizer must keep the
   handler dispatch by exn identity, not collapse the branches. *)
local
  exception A and B and C of int
  fun pick n =
    case n mod 4 of
        0 => raise A
      | 1 => raise B
      | 2 => raise (C n)
      | _ => n
  fun route n =
    (pick n)
    handle A   => ~1
         | B   => ~2
         | C k => k * 100
  fun loop (i, acc) = if i >= 16 then acc else loop (i + 1, acc + route i)
in
  val () = print ("@@nested_ctor=" ^ Int.toString (loop (0, 0)) ^ "\n")
end

(* 5: exception for early exit from a fold (findFirst) — find first index whose
   running product exceeds a bound; the raise must short-circuit the recursion. *)
local
  exception Found of int
  fun search (xs, prod, idx) =
    case xs of
        [] => ~1
      | x :: rest =>
          let val p = prod * x
          in if p > 100000 then raise Found idx
             else search (rest, p, idx + 1)
          end
  val data = [2,3,5,7,11,13,17,19,23,29,31,37]
  val result = search (data, 1, 0) handle Found i => i
in
  val () = print ("@@findfirst=" ^ Int.toString result ^ "\n")
end

(* 6: locally-declared exception inside a function — each call gets fresh
   generativity; ensure a packet raised in one call isn't caught by another's
   handler (constructor identity is per-elaboration here, same exn though). *)
local
  fun mk seed =
    let
      exception Local of int
      fun go n = if n = 0 then raise Local seed else go (n - 1) handle Local k => k
    in
      go 5
    end
  fun loop (i, acc) = if i > 8 then acc else loop (i + 1, acc + mk (i * 11))
in
  val () = print ("@@localexn=" ^ Int.toString (loop (1, 0)) ^ "\n")
end

(* 7: exception inside a closure captured and invoked later; deep recursion with
   handler unwinding many frames at once. *)
local
  exception Deep of int
  fun build d = fn () => if d = 0 then raise Deep 777 else (build (d - 1)) ()
  fun run () = (build 500) () handle Deep k => k
in
  val () = print ("@@deepunwind=" ^ Int.toString (run ()) ^ "\n")
end

(* 8: handler that pattern-matches the packet AND falls through to a default for
   unmatched constructors via a top-level re-raise pattern. *)
local
  exception E1 of int and E2 of string and E3
  fun classify n =
    if n < 0 then raise E1 n
    else if n = 0 then raise E3
    else raise (E2 (Int.toString n))
  fun handleOne n =
    (classify n; 0)
    handle E1 k => k
         | E2 s => String.size s
         | E3   => 999
  val vals = [~5, 0, 42, ~100, 7]
  val tot = foldl (fn (n, a) => a + handleOne n) 0 vals
in
  val () = print ("@@pkt_match=" ^ Int.toString tot ^ "\n")
end

(* 9: exception used to break out of a doubly-nested loop (matrix scan) — find
   first cell (i*j) divisible by 91, return i*100+j. *)
local
  exception Hit of int * int
  fun scan () =
    let
      fun col (i, j) =
        if j > 30 then ()
        else if (i * j) mod 91 = 0 andalso i * j > 0 then raise Hit (i, j)
        else col (i, j + 1)
      fun row i = if i > 30 then () else (col (i, 1); row (i + 1))
    in
      (row 1; ~1) handle Hit (i, j) => i * 100 + j
    end
in
  val () = print ("@@matrix_break=" ^ Int.toString (scan ()) ^ "\n")
end

(* 10: raise within the argument of an arithmetic op; handler recovers a default.
   The optimizer must not reorder the raise past the arithmetic. *)
local
  exception Veto
  fun checked n = if n = 13 then raise Veto else n * n
  fun acc (i, s) =
    if i > 20 then s
    else acc (i + 1, s + (checked i handle Veto => ~1000))
in
  val () = print ("@@arith_raise=" ^ Int.toString (acc (1, 0)) ^ "\n")
end

(* 11: a state machine driven by exceptions — each exn transitions and re-raises
   a different one until a terminal state; counts transitions. *)
local
  exception SA of int and SB of int and SC of int and Done of int
  (* a transition takes a thunk that raises the current state's exn; it handles
     it and returns the next thunk plus a terminal flag. *)
  fun step thunk =
    (thunk () : unit; raise Done ~1)  (* thunk always raises *)
    handle
        SA n => if n > 5 then raise (Done n) else (fn () => raise (SB (n + 1)))
      | SB n => (fn () => raise (SC (n + 2)))
      | SC n => (fn () => raise (SA (n + 1)))
  fun drive (thunk, count) =
    let val next = step thunk
    in drive (next, count + 1) end
    handle Done v => v * 1000 + count
  val result = drive (fn () => raise (SA 0), 0)
in
  val () = print ("@@statemachine=" ^ Int.toString result ^ "\n")
end

(* 12: andb-shape — replicate the exact "if isShort i andalso isShort j then
   word-path else rts-path" pattern that mis-compiled. Use RunCall.isShort and
   verify a hand-rolled bitwise-and over (small,big) and (big,big) and
   (small,small), guarded by an exception when the short-path would truncate. *)
local
  exception Truncated of int
  (* hand-rolled "andb" mirroring the historical shape: if both short, the
     compiler emitted a word-path; else an rts path. We compute via IntInf and
     bring the result back into the default int domain so the optimizer sees the
     same isShort-guarded structure that mis-compiled. *)
  fun myAndb (i: int, j: int) : int =
    if RunCall.isShort i andalso RunCall.isShort j
    then IntInf.toInt (IntInf.andb (IntInf.fromInt i, IntInf.fromInt j))
    else IntInf.toInt (IntInf.andb (IntInf.fromInt i, IntInf.fromInt j))
  (* Guard that raises if andb yields an unexpected value (would fire on the
     historical truncation bug). *)
  fun guarded (i, j, expect) =
    let val r = myAndb (i, j)
    in if r = expect then r else raise (Truncated r) end
  val big = valOf Int.maxInt  (* large within FixedInt, still short *)
  val expBig = IntInf.toInt (IntInf.andb (IntInf.fromInt big, 1))
  val checks =
    [ guarded (255, 240, 240)
    , guarded (big, 1, expBig)
    , guarded (1024, 1023, 0)
    , guarded (~1, 255, 255) ]
  val tot = foldl op+ 0 checks handle Truncated v => ~999999 + v
in
  val () = print ("@@andb_shape=" ^ Int.toString tot ^ "\n")
end

(* 13: handler list with guard-like conditions encoded via re-raise; the inner
   handler conditionally re-raises based on the carried value's parity. *)
local
  exception Val of int
  fun process n =
    (raise (Val n))
    handle Val k => if k mod 2 = 0 then k else raise (Val (k + 1000))
  fun safe n = process n handle Val k => k
  fun loop (i, acc) = if i > 12 then acc else loop (i + 1, acc + safe i)
in
  val () = print ("@@guarded_reraise=" ^ Int.toString (loop (1, 0)) ^ "\n")
end

(* 14: exception thrown across a higher-order map; List.map's traversal must be
   abandoned cleanly and the partial work discarded. *)
local
  exception Negative of int
  fun transform xs =
    (List.map (fn x => if x < 0 then raise (Negative x) else x * x) xs; ~1)
    handle Negative v => v
  val r1 = transform [1,2,3,4,5]          (* no neg -> ~1 *)
  val r2 = transform [1,2,~7,4,5]         (* hits ~7 *)
  val r3 = transform [~3, ~9]             (* first neg ~3 *)
in
  val () = print ("@@map_raise=" ^ Int.toString (r1 + r2 + r3) ^ "\n")
end

(* 15: deeply nested try/handle with finally-style cleanup via refs; ensure the
   cleanup runs the correct number of times regardless of which arm raises. *)
local
  exception Fail
  val cleanups = ref 0
  fun withCleanup body =
    let
      val r = (body () handle e => (cleanups := !cleanups + 1; raise e))
    in
      cleanups := !cleanups + 1; r
    end
  fun attempt n =
    (withCleanup (fn () => if n mod 4 = 0 then raise Fail else n))
    handle Fail => ~1
  fun loop (i, acc) = if i > 10 then acc else loop (i + 1, acc + attempt i)
in
  val s = loop (1, 0)
  val () = print ("@@finally_cleanups=" ^ Int.toString (s * 100 + !cleanups) ^ "\n")
end

(* 16: a parser-ish recursive descent that uses an exception for parse errors,
   recovering and continuing — counts successes and the error positions. *)
local
  exception ParseErr of int
  (* "parse" a list of ints: each must be < 50, else error at its position *)
  fun parseOne (pos, x) = if x < 50 then x else raise (ParseErr pos)
  fun parseAll xs =
    let
      fun go ([], _, ok, errsum) = (ok, errsum)
        | go (x :: rest, pos, ok, errsum) =
            let
              val (ok', errsum') =
                (parseOne (pos, x); (ok + x, errsum))
                handle ParseErr p => (ok, errsum + p)
            in go (rest, pos + 1, ok', errsum') end
    in go (xs, 0, 0, 0) end
  val (ok, errs) = parseAll [10, 99, 20, 60, 30, 5, 77]
in
  val () = print ("@@parser_recover=" ^ Int.toString (ok * 1000 + errs) ^ "\n")
end

(* 17: exception with a function payload (exn carrying a closure) — invoke the
   carried thunk in the handler. Tests closure capture through the packet. *)
local
  exception Thunk of unit -> int
  fun make n = raise (Thunk (fn () => n * n + 1))
  fun run n = (make n; 0) handle Thunk f => f ()
  fun loop (i, acc) = if i > 9 then acc else loop (i + 1, acc + run i)
in
  val () = print ("@@thunk_payload=" ^ Int.toString (loop (1, 0)) ^ "\n")
end

(* 18: stress overflow exception interplay — checked addition that catches
   Overflow and the handler still runs in a tight accumulation. Uses FixedInt
   default ints near maxInt to force genuine Overflow. *)
local
  val mx = valOf Int.maxInt
  fun safeAdd (a, b) = (a + b) handle Overflow => ~1
  val results =
    [ safeAdd (mx, 1)          (* overflow -> ~1 *)
    , safeAdd (100, 200)       (* 300 *)
    , safeAdd (mx, ~1)         (* mx-1 *)
    , safeAdd (mx - 5, 10) ]   (* overflow -> ~1 *)
  (* normalize: count overflows and sum the non-overflow proper results' parity *)
  val overflows = foldl (fn (x, a) => if x = ~1 then a + 1 else a) 0 results
  val proper = foldl (fn (x, a) => if x <> ~1 then a + (x mod 7) else a) 0 results
in
  val () = print ("@@overflow_catch=" ^ Int.toString (overflows * 100 + proper) ^ "\n")
end

(* 19: real-valued computation guarded by exceptions, deterministic via Real.fmt;
   a Domain-style exception for sqrt of negatives (hand-checked) recovers 0.0. *)
local
  exception NegSqrt
  fun mySqrt x = if x < 0.0 then raise NegSqrt else Math.sqrt x
  fun guarded x = (mySqrt x) handle NegSqrt => 0.0
  val xs = [4.0, ~9.0, 16.0, 2.0, ~1.0, 25.0]
  val total = foldl (fn (x, a) => a + guarded x) 0.0 xs
in
  val () = print ("@@real_guard=" ^ Real.fmt (StringCvt.FIX (SOME 8)) total ^ "\n")
end

(* 20: combined torture — datatype tree, recursive evaluator with exceptions for
   division by zero and unbound variables, environment as assoc list, exception
   propagation up the tree with selective recovery. *)
local
  datatype expr = Num of int
                | Var of string
                | Add of expr * expr
                | Div of expr * expr
                | Try of expr * expr   (* eval first; on any error eval second *)
  exception DivZero and Unbound of string
  fun lookup ([], x) = raise (Unbound x)
    | lookup ((k, v) :: rest, x) = if k = x then v else lookup (rest, x)
  fun eval (env, e) =
    case e of
        Num n => n
      | Var x => lookup (env, x)
      | Add (a, b) => eval (env, a) + eval (env, b)
      | Div (a, b) =>
          let val d = eval (env, b)
          in if d = 0 then raise DivZero else eval (env, a) div d end
      | Try (a, b) => (eval (env, a) handle DivZero => eval (env, b)
                                          | Unbound _ => eval (env, b))
  val env = [("x", 10), ("y", 0), ("z", 3)]
  val program =
    Add (Try (Div (Var "x", Var "y"), Num 100),     (* div by zero -> 100 *)
         Add (Try (Var "w", Num 7),                  (* unbound -> 7 *)
              Div (Var "x", Var "z")))               (* 10 div 3 = 3 *)
  val result = eval (env, program) handle _ => ~1
in
  val () = print ("@@tree_eval=" ^ Int.toString result ^ "\n")
end
