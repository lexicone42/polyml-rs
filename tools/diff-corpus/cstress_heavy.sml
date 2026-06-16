(* diff-corpus category: cstress_heavy (heavy-compute stress, 2026-06-16)
   Beyond the light Basis edge-case sweep: programs that HAMMER the interpreter
   — deep recursion + tail-call optimization, exponential call counts, bignum
   arithmetic + GC pressure, large allocations, exception unwinding in a loop —
   each reduced to one exact deterministic @@label compared against upstream. *)

(* --- deep recursion + heavy call counts --- *)
fun ack 0 n = n + 1
  | ack m 0 = ack (m - 1) 1
  | ack m n = ack (m - 1) (ack m (n - 1));
val () = print ("@@ackermann_3_6=" ^ Int.toString (ack 3 6) ^ "\n");   (* 509 *)
val () = print ("@@ackermann_3_7=" ^ Int.toString (ack 3 7) ^ "\n");   (* 1021 *)

fun fib 0 = 0 | fib 1 = 1 | fib n = fib (n - 1) + fib (n - 2);
val () = print ("@@fib_naive_30=" ^ Int.toString (fib 30) ^ "\n");     (* 832040 *)
val () = print ("@@fib_naive_34=" ^ Int.toString (fib 34) ^ "\n");     (* 5702887 *)

(* --- tail-call optimization: linear in steps, must NOT grow the stack --- *)
fun sumTail (acc : IntInf.int) 0 = acc
  | sumTail acc n = sumTail (acc + IntInf.fromInt n) (n - 1);
val () = print ("@@sum_tail_1e6=" ^ IntInf.toString (sumTail 0 1000000) ^ "\n"); (* 500000500000 *)

(* mutual tail recursion 100k deep (TCO required, else stack blows) *)
fun isEven 0 = true | isEven n = isOdd (n - 1)
and isOdd 0 = false | isOdd n = isEven (n - 1);
val () = print ("@@mutual_even_100k=" ^ Bool.toString (isEven 100000) ^ "\n");
val () = print ("@@mutual_odd_100k=" ^ Bool.toString (isOdd 100000) ^ "\n");

(* --- bignum arithmetic + GC pressure --- *)
fun factI (n : IntInf.int) = if n <= 0 then 1 else n * factI (n - 1);
val f100 = factI 100;
val f50 = factI 50;
val () = print ("@@fact100_str=" ^ IntInf.toString f100 ^ "\n");
val () = print ("@@fact200_numdigits="
  ^ Int.toString (String.size (IntInf.toString (factI 200))) ^ "\n");

fun ipow (b : IntInf.int) 0 = 1 | ipow b e = b * ipow b (e - 1);
val () = print ("@@pow2_1000=" ^ IntInf.toString (ipow 2 1000) ^ "\n");
val () = print ("@@pow3_500_numdigits="
  ^ Int.toString (String.size (IntInf.toString (ipow 3 500))) ^ "\n");

fun gcdI (a : IntInf.int) (b : IntInf.int) = if b = 0 then a else gcdI b (a mod b);
(* 50! divides 100!, so gcd(100!,50!) = 50! *)
val () = print ("@@gcd_fact100_fact50_eq_fact50="
  ^ Bool.toString (gcdI f100 f50 = f50) ^ "\n");
val () = print ("@@gcd_big=" ^ IntInf.toString (gcdI (ipow 2 600) (ipow 2 400 * ipow 3 10)) ^ "\n");

(* repeated-squaring modular exponentiation on a big modulus (number-theory flavour) *)
fun powmod (b : IntInf.int) e (m : IntInf.int) =
  if e = 0 then 1 mod m
  else let val h = powmod b (e div 2) m
           val h2 = (h * h) mod m
       in if e mod 2 = 1 then (h2 * b) mod m else h2 end;
val () = print ("@@powmod_7_pow_1000_mod_big="
  ^ IntInf.toString (powmod 7 1000 (ipow 10 30 + 1)) ^ "\n");

(* --- large allocation / fold over a big list (alloc + GC) --- *)
val big = List.tabulate (100000, fn i => i);
val () = print ("@@foldl_sum_100k=" ^ Int.toString (foldl (op +) 0 big) ^ "\n"); (* 4999950000 *)
val () = print ("@@map_filter_len="
  ^ Int.toString (length (List.filter (fn x => x mod 7 = 0) (map (fn x => x * 2) big))) ^ "\n");
val () = print ("@@rev_then_hd=" ^ Int.toString (hd (rev big)) ^ "\n");   (* 99999 *)

(* --- exception raise/handle in a tight loop (unwinding stress) --- *)
fun exLoop 0 acc = acc
  | exLoop n acc = exLoop (n - 1) ((raise Subscript) handle Subscript => acc + 1);
val () = print ("@@exn_loop_100k=" ^ Int.toString (exLoop 100000 0) ^ "\n"); (* 100000 *)

exception Tagged of int;
fun exPayload 0 acc = acc
  | exPayload n acc = exPayload (n - 1) ((raise Tagged n) handle Tagged k => acc + k);
val () = print ("@@exn_payload_sum_1k=" ^ Int.toString (exPayload 1000 0) ^ "\n"); (* 500500 *)

(* --- conditional-heavy loop (Collatz) --- *)
fun collatz 1 steps = steps
  | collatz n steps = collatz (if n mod 2 = 0 then n div 2 else 3 * n + 1) (steps + 1);
val () = print ("@@collatz_27_steps=" ^ Int.toString (collatz 27 0) ^ "\n");   (* 111 *)
val () = print ("@@collatz_97_steps=" ^ Int.toString (collatz 97 0) ^ "\n");   (* 118 *)

(* --- higher-order: function composition iterated, Church-ish --- *)
fun iterate f 0 x = x | iterate f n x = iterate f (n - 1) (f x);
val () = print ("@@iterate_succ_1e6="
  ^ IntInf.toString (iterate (fn x => x + 1) 1000000 (0 : IntInf.int)) ^ "\n");
val () = print ("@@iterate_double_30="
  ^ IntInf.toString (iterate (fn x => x * 2) 30 (1 : IntInf.int)) ^ "\n"); (* 2^30 *)
