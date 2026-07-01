(* ray — a minimal ray tracer: a fixed scene of 4 spheres, one directional
 * light, Lambertian shading, a pinhole camera rendering an n*n image.
 * bench n = sum over pixels of the quantized (0..255) shade intensity.
 *
 * Only +,-,*,/,sqrt and Real.round are used (all correctly rounded on
 * bit-identical inputs -> deterministic across engines); the checksum is an
 * integer, robust to real-formatting differences. A float + light-branching
 * inner-loop benchmark. *)

fun ray n =
    let
      fun sub ((ax,ay,az),(bx,by,bz)) = (ax-bx, ay-by, az-bz)
      fun add ((ax,ay,az),(bx,by,bz)) = (ax+bx, ay+by, az+bz)
      fun scale (s,(x,y,z)) = (s*x, s*y, s*z)
      fun dot ((ax,ay,az),(bx,by,bz)) = ax*bx + ay*by + az*bz
      fun len v = Math.sqrt (dot (v, v))
      fun norm v = scale (1.0 / len v, v)
      (* scene: (center, radius, albedo) *)
      val spheres = [ ((0.0,  0.0, ~5.0),   1.0, 0.8),
                      ((2.0,  0.0, ~6.0),   1.2, 0.6),
                      ((~2.0, 1.0, ~7.0),   1.5, 0.7),
                      ((0.0, ~101.0, ~5.0), 100.0, 0.5) ]   (* ground plane *)
      val light = norm (1.0, 1.0, ~1.0)
      val eye = (0.0, 0.0, 0.0)
      fun hit (orig, dir, (c, r, _)) =
          let val oc = sub (orig, c)
              val a = dot (dir, dir)
              val b = 2.0 * dot (oc, dir)
              val cc = dot (oc, oc) - r * r
              val disc = b * b - 4.0 * a * cc
          in if disc < 0.0 then NONE
             else
               let val t = (~b - Math.sqrt disc) / (2.0 * a)
               in if t > 0.001 then SOME t else NONE end
          end
      fun nearest (orig, dir) =
          let fun go ([], best) = best
                | go (s :: rest, best) =
                    (case hit (orig, dir, s) of
                         NONE => go (rest, best)
                       | SOME t =>
                           (case best of
                                NONE => go (rest, SOME (t, s))
                              | SOME (bt, _) =>
                                  if t < bt then go (rest, SOME (t, s)) else go (rest, best)))
          in go (spheres, NONE) end
      fun shade (orig, dir) =
          case nearest (orig, dir) of
              NONE => 0
            | SOME (t, (c, _, alb)) =>
                let val p   = add (orig, scale (t, dir))
                    val nrm = norm (sub (p, c))
                    val d0  = dot (nrm, light)
                    val d   = if d0 < 0.0 then 0.0 else d0
                    val v   = Real.round (alb * d * 255.0)
                in if v < 0 then 0 else if v > 255 then 255 else v end
      val rn = Real.fromInt n
      fun pixel (i, j) =
          let val cx = ~1.0 + 2.0 * Real.fromInt j / rn
              val cy =  1.0 - 2.0 * Real.fromInt i / rn
          in shade (eye, norm (cx, cy, ~1.0)) end
      fun loop (i, j, acc) =
          if i >= n then acc
          else if j >= n then loop (i + 1, 0, acc)
          else loop (i, j + 1, acc + pixel (i, j))
    in loop (0, 0, 0) end;

fun bench n = ray n;
fun checksum (r:int) = Int.toString r;

val bench_name = "bench_ray";
val default_n  = 64;
