(* mmult — dense n*n integer matrix multiply over flat Arrays (row-major).
 * A and B are filled deterministically from their indices (mod 100), so entries
 * and products stay small (fixnum fast path). checksum = full sum of C mod 1e9+7.
 * A tight nested-loop + array-indexing benchmark. *)

fun mmult n =
    let
      val A = Array.tabulate (n * n, fn t => ((t div n) * 7 + (t mod n) * 3 + 1) mod 100)
      val B = Array.tabulate (n * n, fn t => ((t div n) * 5 + (t mod n) * 11 + 2) mod 100)
      val C = Array.array (n * n, 0)
      fun cell (i, j) =
          let fun go (k, acc) =
                  if k = n then acc
                  else go (k + 1, acc + Array.sub (A, i * n + k) * Array.sub (B, k * n + j))
          in go (0, 0) end
      fun cols (i, j) =
          if j = n then ()
          else (Array.update (C, i * n + j, cell (i, j)); cols (i, j + 1))
      fun rows i = if i = n then () else (cols (i, 0); rows (i + 1))
      val () = rows 0
      fun sumAll (t, acc) =
          if t = n * n then acc else sumAll (t + 1, (acc + Array.sub (C, t)) mod 1000000007)
    in sumAll (0, 0) end;

fun bench n = mmult n;
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_mmult";
val default_n  = 40;
