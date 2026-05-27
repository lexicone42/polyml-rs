(* Conway's Game of Life. Starts with a glider; runs 12 generations.
 * The glider should walk diagonally down-right across the grid.
 * Period-4 motion: every 4 generations it shifts by (+1, +1). *)

val rows = 12;
val cols = 22;

(* Encode grid as a 2D array. *)
fun make_grid () = Array.array (rows * cols, false);
fun idx (r, c) = r * cols + c;

fun get g (r, c) =
    if r < 0 orelse r >= rows orelse c < 0 orelse c >= cols
    then false
    else Array.sub (g, idx (r, c));

fun set g (r, c) v = Array.update (g, idx (r, c), v);

fun count_neighbours g (r, c) =
    let val deltas = [(~1,~1),(~1,0),(~1,1),(0,~1),(0,1),(1,~1),(1,0),(1,1)]
    in List.foldl
        (fn ((dr, dc), n) => if get g (r + dr, c + dc) then n + 1 else n)
        0 deltas
    end;

fun step old =
    let val new = make_grid ()
        fun loop_c r c =
            if c >= cols then ()
            else
                let val alive = get old (r, c)
                    val n = count_neighbours old (r, c)
                    val next =
                        if alive then n = 2 orelse n = 3
                        else n = 3
                in set new (r, c) next;
                   loop_c r (c + 1)
                end
        fun loop_r r =
            if r >= rows then ()
            else (loop_c r 0; loop_r (r + 1))
        val () = loop_r 0
    in new end;

fun show g =
    let fun row r =
            String.implode (List.tabulate (cols, fn c =>
                if get g (r, c) then #"#" else #"."))
        val border = String.implode (List.tabulate (cols + 2, fn _ => #"-"))
    in print (border ^ "\n");
       List.app (fn r => print ("|" ^ row r ^ "|\n"))
                (List.tabulate (rows, fn r => r));
       print (border ^ "\n")
    end;

(* Place a glider at top-left. *)
val g = make_grid ();
val () = set g (0, 1) true;
val () = set g (1, 2) true;
val () = set g (2, 0) true;
val () = set g (2, 1) true;
val () = set g (2, 2) true;

fun run_n g 0 = g
  | run_n g n =
      (print ("\nGeneration " ^ Int.toString (12 - n) ^ ":\n");
       show g;
       run_n (step g) (n - 1));

val _ = run_n g 12;
print "\nGlider walked diagonally across the grid.\n";
