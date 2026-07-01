(* queens — count all solutions to the n-queens problem by backtracking.
 * bench n = number of distinct solutions on an n*n board. Pure integer/list.
 * A famous exponential-search benchmark; deterministic. *)

fun queens n =
    let
      (* board = rows chosen for the already-placed columns, most recent first *)
      fun safe (_, _, []) = true
        | safe (r, d, q :: qs) =
            r <> q andalso r <> q + d andalso r <> q - d andalso safe (r, d + 1, qs)
      fun solve (board, ncols) =
          if ncols = n then 1
          else
            let
              fun tryRow (0, acc) = acc
                | tryRow (r, acc) =
                    tryRow (r - 1,
                            if safe (r, 1, board) then acc + solve (r :: board, ncols + 1)
                            else acc)
            in tryRow (n, 0) end
    in solve ([], 0) end;

fun bench n = queens n;
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_queens";
val default_n  = 8;
