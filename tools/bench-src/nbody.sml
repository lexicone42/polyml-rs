(* nbody — direct O(n^2) gravitational N-body with a leapfrog integrator.
 *
 * NB: the classic SML/NJ benchmark is "barnes-hut", the O(n log n) octree
 * approximation. A faithful octree port is large and error-prone; the direct
 * O(n^2) sum exercises the SAME profile that matters here — a floating-point
 * inner loop over sqrt/mul/div — with a simple, obviously-correct kernel, so we
 * use it instead and name it honestly. bench n = number of bodies (10 steps).
 *
 * Only +,-,*,/,sqrt are used (all IEEE correctly-rounded, hence bit-identical
 * across engines); the checksum is the sum of quantized final positions (an
 * integer, robust to real-formatting differences). Bodies and velocities are
 * seeded by a fixed LCG, so the whole run is deterministic. *)

fun nbody nbodies =
    let
      val steps = 10
      val dt   = 0.01
      val eps2 = 0.0001                (* softening^2, avoids the r->0 singularity *)
      val g    = 1.0
      val px = Array.array (nbodies, 0.0) and py = Array.array (nbodies, 0.0)
      and pz = Array.array (nbodies, 0.0)
      val vx = Array.array (nbodies, 0.0) and vy = Array.array (nbodies, 0.0)
      and vz = Array.array (nbodies, 0.0)
      val mass = Array.array (nbodies, 0.0)
      fun lcg s = (s * 1103515245 + 12345) mod 2147483648
      fun unit s = Real.fromInt s / 2147483648.0     (* [0,1) *)
      fun init (i, s) =
          if i = nbodies then ()
          else
            let val s1 = lcg s  val s2 = lcg s1 val s3 = lcg s2 val s4 = lcg s3
                val s5 = lcg s4 val s6 = lcg s5 val s7 = lcg s6
            in
              Array.update (px, i, unit s1 * 2.0 - 1.0);
              Array.update (py, i, unit s2 * 2.0 - 1.0);
              Array.update (pz, i, unit s3 * 2.0 - 1.0);
              Array.update (vx, i, (unit s4 - 0.5) * 0.1);
              Array.update (vy, i, (unit s5 - 0.5) * 0.1);
              Array.update (vz, i, (unit s6 - 0.5) * 0.1);
              Array.update (mass, i, unit s7 + 0.5);
              init (i + 1, s7)
            end
      val () = init (0, 1)
      fun accel i =
          let fun go (j, ax, ay, az) =
                  if j = nbodies then (ax, ay, az)
                  else if j = i then go (j + 1, ax, ay, az)
                  else
                    let val dx = Array.sub (px, j) - Array.sub (px, i)
                        val dy = Array.sub (py, j) - Array.sub (py, i)
                        val dz = Array.sub (pz, j) - Array.sub (pz, i)
                        val r2 = dx * dx + dy * dy + dz * dz + eps2
                        val r  = Math.sqrt r2
                        val f  = g * Array.sub (mass, j) / (r2 * r)
                    in go (j + 1, ax + f * dx, ay + f * dy, az + f * dz) end
          in go (0, 0.0, 0.0, 0.0) end
      fun updateV i =
          if i = nbodies then ()
          else
            let val (ax, ay, az) = accel i
            in Array.update (vx, i, Array.sub (vx, i) + ax * dt);
               Array.update (vy, i, Array.sub (vy, i) + ay * dt);
               Array.update (vz, i, Array.sub (vz, i) + az * dt);
               updateV (i + 1)
            end
      fun updateP i =
          if i = nbodies then ()
          else (Array.update (px, i, Array.sub (px, i) + Array.sub (vx, i) * dt);
                Array.update (py, i, Array.sub (py, i) + Array.sub (vy, i) * dt);
                Array.update (pz, i, Array.sub (pz, i) + Array.sub (vz, i) * dt);
                updateP (i + 1))
      fun run 0 = ()
        | run k = (updateV 0; updateP 0; run (k - 1))
      val () = run steps
      fun hash (i, acc) =
          if i = nbodies then acc
          else
            let val q = Real.toLargeInt IEEEReal.TO_NEAREST
                          ((Array.sub (px, i) + Array.sub (py, i) + Array.sub (pz, i)) * 1000000.0)
            in hash (i + 1, (acc + q) mod 1000000007) end
    in hash (0, 0) end;

fun bench n = nbody n;
fun checksum (r:LargeInt.int) = LargeInt.toString r;

val bench_name = "bench_nbody";
val default_n  = 40;
