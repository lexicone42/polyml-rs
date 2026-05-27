(* N-Queens solver via recursive backtracking.
 * Returns all solutions as lists of column-positions.
 *
 * Verifies count for N=8 (should be 92 — the classical result).
 *
 * Run via:
 *   ./target/release/poly run --max-steps 100000000 /tmp/basis_loaded < demos/queens.sml *)

(* `safe c row qs`: can we place at column c on `row`, given queens
   at (1, qs[0]), (2, qs[1]), ... already placed?
   qs is in reverse-row order so qs[0] is the most recent. *)
fun safe c qs =
    let fun chk _ [] = true
          | chk d (q :: rest) =
              c <> q
              andalso c <> q + d
              andalso c <> q - d
              andalso chk (d + 1) rest
    in chk 1 qs end;

(* For each partial-solution, extend with all valid next-row choices. *)
fun nqueens n =
    let fun extend [] = []
          | extend (qs :: rest) =
              let val n_placed = List.length qs
              in if n_placed = n
                 then qs :: extend rest
                 else
                     let val candidates =
                             List.tabulate (n, fn i => i + 1)
                         val valid =
                             List.filter (fn c => safe c qs) candidates
                         val extended =
                             List.map (fn c => c :: qs) valid
                     in extended @ extend rest end
              end
        fun loop partial =
            if List.exists (fn qs => List.length qs < n) partial
            then loop (extend partial)
            else partial
    in loop [[]] end;

fun show_solution qs =
    let val rows = List.rev qs (* row 1 first *)
        fun show_row q n =
            String.implode (List.tabulate (n, fn i =>
                if i + 1 = q then #"Q" else #"."))
        val n = List.length qs
        val lines = List.map (fn q => show_row q n) rows
    in String.concatWith "\n" lines end;

(* Solve N=6 — small enough to print all solutions. *)
val sols = nqueens 6;
print ("N-Queens for N=6: " ^ Int.toString (List.length sols)
       ^ " solutions\n\n");
print ("First solution:\n" ^ show_solution (hd sols) ^ "\n\n");

(* Just count for N=8 — too many to print. *)
val sols8 = nqueens 8;
print ("N-Queens for N=8: " ^ Int.toString (List.length sols8)
       ^ " solutions (expected: 92)\n");
