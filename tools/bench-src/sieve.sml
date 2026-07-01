(* sieve — Sieve of Eratosthenes over a boolean Array up to n.
 * bench n = (count of primes <= n, sum of those primes mod 1e9+7).
 * Array-mutation + tight integer loop benchmark; deterministic. *)

fun sieve n =
    let
      val a = Array.array (n + 1, true)
      val () = if n >= 0 then Array.update (a, 0, false) else ()
      val () = if n >= 1 then Array.update (a, 1, false) else ()
      fun mark (p, k) = if k > n then () else (Array.update (a, k, false); mark (p, k + p))
      fun loop p =
          if p * p > n then ()
          else (if Array.sub (a, p) then mark (p, p * p) else (); loop (p + 1))
      val () = loop 2
      fun tally (i, cnt, s) =
          if i > n then (cnt, s)
          else if Array.sub (a, i) then tally (i + 1, cnt + 1, (s + i) mod 1000000007)
          else tally (i + 1, cnt, s)
    in tally (0, 0, 0) end;

fun bench n = sieve n;
fun checksum (cnt, s) = Int.toString cnt ^ ":" ^ Int.toString s;

val bench_name = "bench_sieve";
val default_n  = 200000;
