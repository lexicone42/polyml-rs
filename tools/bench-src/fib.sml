(* fib — naive (non-tail) integer recursion. Classic SML/NJ micro-benchmark.
 * bench n = fib n; checksum = the value. Pure integer arithmetic. *)

fun fib n = if n < 2 then n else fib (n - 1) + fib (n - 2);

fun bench n = fib n;
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_fib";
val default_n  = 27;
