(* Mandelbrot set, rendered in ASCII.
 *
 * For each pixel (x, y) in the viewport, iterate z := z^2 + c starting
 * from z = 0+0i, where c = x + y*i. Count iterations until |z| > 2 or
 * we hit max_iter. Pixels that escape quickly are background; pixels
 * that stay bounded for many iterations are the set itself.
 *
 * Exercises Real arithmetic, recursion, higher-order list ops. Runs in
 * ~1 second on a 78x24 viewport with 32 iterations max.
 *
 * Run via:
 *   ./target/release/poly run --max-steps 200000000 \
 *     /tmp/basis_loaded < demos/mandel.sml *)

val max_iter = 32;
val width = 78;
val height = 24;
val x_min = ~2.2;
val x_max = 1.0;
val y_min = ~1.1;
val y_max = 1.1;

(* Returns the iteration count at which |z| > 2, or max_iter if it stays
 * bounded for the whole budget. *)
fun mandel_iters (cx, cy) =
    let fun loop (zx, zy, n) =
            if n >= max_iter then max_iter
            else
                let val zx2 = zx * zx
                    val zy2 = zy * zy
                in if zx2 + zy2 > 4.0 then n
                   else
                       let val new_zx = zx2 - zy2 + cx
                           val new_zy = 2.0 * zx * zy + cy
                       in loop (new_zx, new_zy, n + 1) end
                end
    in loop (0.0, 0.0, 0) end;

(* Map an iteration count to a character — denser characters for points
 * deeper inside the set. *)
fun shade n =
    let val chars = " .,:;ox%#@" (* 10 chars *)
        val idx = if n >= max_iter then 9
                  else (n * 9) div max_iter
    in String.sub (chars, idx) end;

fun render () =
    let val () = print ("Mandelbrot set (" ^ Int.toString width ^ "x"
                        ^ Int.toString height ^ ", "
                        ^ Int.toString max_iter ^ " iters)\n");
        fun row r =
            let val cy = y_min + (y_max - y_min) * Real.fromInt r
                                 / Real.fromInt (height - 1)
                fun pix c =
                    let val cx = x_min + (x_max - x_min) * Real.fromInt c
                                         / Real.fromInt (width - 1)
                        val n = mandel_iters (cx, cy)
                    in print (String.str (shade n)) end
            in List.app pix (List.tabulate (width, fn i => i));
               print "\n"
            end
    in List.app row (List.tabulate (height, fn i => i)) end;

val () = render ();
