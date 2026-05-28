(* Sudoku solver via backtracking with constraint propagation.
 *
 * Encodes the board as a 9x9 array (0 = empty, 1-9 = filled). For each
 * empty cell, tries 1..9 in order, checking that the digit is
 * consistent with row/column/3x3-block constraints.
 *
 * Test input: Arto Inkala's "World's Hardest Sudoku" (2012), designed
 * to defeat naive backtrackers. Solves in ~3 seconds (253M bytecode
 * steps) on the polyml-rs runtime.
 *
 * Run via:
 *   ./target/release/poly run --max-steps 500000000 \
 *     /tmp/basis_loaded < demos/sudoku.sml *)

(* Hard puzzle: each list is a row, 0 = empty. *)
val puzzle = [
    [8,0,0, 0,0,0, 0,0,0],
    [0,0,3, 6,0,0, 0,0,0],
    [0,7,0, 0,9,0, 2,0,0],

    [0,5,0, 0,0,7, 0,0,0],
    [0,0,0, 0,4,5, 7,0,0],
    [0,0,0, 1,0,0, 0,3,0],

    [0,0,1, 0,0,0, 0,6,8],
    [0,0,8, 5,0,0, 0,1,0],
    [0,9,0, 0,0,0, 4,0,0]
];

(* Flatten into a 81-cell array. *)
fun build_board () =
    let val arr = Array.array (81, 0)
        fun fill r =
            if r = 9 then ()
            else
                let val row = List.nth (puzzle, r)
                    fun col c =
                        if c = 9 then ()
                        else (Array.update (arr, r * 9 + c, List.nth (row, c));
                              col (c + 1))
                in col 0; fill (r + 1) end
        val () = fill 0
    in arr end;

(* Returns true if placing `v` at row r, col c is consistent. *)
fun ok board (r, c, v) =
    let fun row_clear i =
            i >= 9 orelse (Array.sub (board, r * 9 + i) <> v andalso row_clear (i + 1))
        fun col_clear i =
            i >= 9 orelse (Array.sub (board, i * 9 + c) <> v andalso col_clear (i + 1))
        val br = (r div 3) * 3
        val bc = (c div 3) * 3
        fun block_clear i =
            if i >= 9 then true
            else
                let val rr = br + i div 3
                    val cc = bc + i mod 3
                in Array.sub (board, rr * 9 + cc) <> v andalso block_clear (i + 1) end
    in row_clear 0 andalso col_clear 0 andalso block_clear 0 end;

(* Solve in place via backtracking. Returns true on success. *)
fun solve board =
    let fun next_empty i =
            if i >= 81 then ~1
            else if Array.sub (board, i) = 0 then i
            else next_empty (i + 1)
        val i = next_empty 0
    in
        if i < 0 then true
        else
            let val r = i div 9
                val c = i mod 9
                fun try v =
                    if v > 9 then false
                    else if ok board (r, c, v)
                    then (Array.update (board, i, v);
                          if solve board then true
                          else (Array.update (board, i, 0); try (v + 1)))
                    else try (v + 1)
            in try 1 end
    end;

fun show board =
    let fun row r =
            let val cells = List.tabulate (9, fn c =>
                let val v = Array.sub (board, r * 9 + c)
                in (if v = 0 then "." else Int.toString v) end)
                fun group i =
                    if i >= 9 then ""
                    else
                        (if i > 0 andalso i mod 3 = 0 then "| " else "")
                        ^ List.nth (cells, i) ^ " " ^ group (i + 1)
            in print (group 0 ^ "\n") end
    in List.app (fn r =>
        (if r mod 3 = 0 andalso r > 0
         then print "------+-------+------\n" else ();
         row r))
       (List.tabulate (9, fn i => i))
    end;

val board = build_board ();
print "Inkala's 'world's hardest sudoku':\n";
show board;
print "\nSolving...\n\n";
val ok = solve board;
if ok then (print "Solution:\n"; show board)
      else print "No solution found.\n";
