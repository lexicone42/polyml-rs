(* cpstak — the Takeuchi function written in continuation-passing style.
 * Same result as tak but stresses closure allocation and higher-order calls
 * instead of plain recursion. bench n = cpstak (3n, 2n, n). Pure integer. *)

fun cpstak (x, y, z) =
    let
      fun tak (x, y, z, k) =
          if not (y < x) then k z
          else tak (x - 1, y, z, fn v1 =>
               tak (y - 1, z, x, fn v2 =>
               tak (z - 1, x, y, fn v3 =>
               tak (v1, v2, v3, k))))
    in tak (x, y, z, fn a => a) end;

fun bench n = cpstak (3 * n, 2 * n, n);
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_cpstak";
val default_n  = 6;
