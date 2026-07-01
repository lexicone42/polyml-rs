(* tak — the Takeuchi function. Classic recursion/call-overhead benchmark.
 * bench n = tak (3n, 2n, n); the standard case is n=6 -> tak(18,12,6).
 * Pure integer arithmetic; deterministic. *)

fun tak (x, y, z) =
    if not (y < x) then z
    else tak (tak (x - 1, y, z), tak (y - 1, z, x), tak (z - 1, x, y));

fun bench n = tak (3 * n, 2 * n, n);
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_tak";
val default_n  = 6;
