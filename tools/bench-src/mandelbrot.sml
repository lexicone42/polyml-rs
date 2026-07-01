(* mandelbrot — escape-time render of an n*n grid over [-2,1] x [-1.5,1.5].
 * Uses only IEEE +,-,*,/ and a > comparison (all correctly rounded, hence
 * bit-identical across engines), and returns an INTEGER checksum (the sum of
 * per-pixel escape iteration counts). Robust to real-formatting differences.
 * A floating-point inner-loop benchmark. *)

fun mandel n =
    let
      val maxIter = 255
      fun escape (cr, ci) =
          let fun it (zr, zi, k) =
                  if k >= maxIter then maxIter
                  else
                    let val zr2 = zr * zr
                        val zi2 = zi * zi
                    in if zr2 + zi2 > 4.0 then k
                       else it (zr2 - zi2 + cr, 2.0 * zr * zi + ci, k + 1)
                    end
          in it (0.0, 0.0, 0) end
      val rn = Real.fromInt n
      fun px (i, j) =
          let val cr = ~2.0 + 3.0 * Real.fromInt j / rn
              val ci = ~1.5 + 3.0 * Real.fromInt i / rn
          in escape (cr, ci) end
      fun loop (i, j, acc) =
          if i >= n then acc
          else if j >= n then loop (i + 1, 0, acc)
          else loop (i, j + 1, acc + px (i, j))
    in loop (0, 0, 0) end;

fun bench n = mandel n;
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_mandelbrot";
val default_n  = 80;
