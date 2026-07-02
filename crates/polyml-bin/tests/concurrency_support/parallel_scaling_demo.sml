(* PARALLEL compute-scaling probe (P4: the giant lock is dropped under
   POLY_PARALLEL=1).

   Two workers each run a fixed, deterministic, PURE-compute loop (tagged
   ints only — no allocation, no locks in the hot path) and deposit their
   results under a mutex, signalling a condition variable; the main
   thread BLOCKS on the condvar (no busy polling — a polling main would
   burn interpreter turns under the giant lock and a core under
   parallel, distorting the A/B wall-clock comparison).

   The RESULT VALUES are the discriminator: spin is deterministic, so
   the harness asserts the giant-lock run and the parallel run print
   byte-identical result lines — same computation, different schedule.
   The harness measures wall-clock around each run: under the giant
   lock the workers serialize; with POLY_PARALLEL=1 they genuinely run
   on two cores.                                                        *)

structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;

val iters = 60000000;

fun spin (acc, 0) = acc
  | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);

val m  = M.mutex ();
val cv = C.conditionVar ();
val nDone = ref 0;
val r1 = ref 0 and r2 = ref 0;

fun worker (r, seed) () =
  let
    val v = spin (seed, iters)
  in
    M.lock m; r := v; nDone := !nDone + 1; C.signal cv; M.unlock m
  end;

val () = ignore (T.fork (worker (r1, 1), []));
val () = ignore (T.fork (worker (r2, 2), []));
val () = (M.lock m;
          while !nDone < 2 do C.wait (cv, m);
          M.unlock m);

val () = print ("spin results: r1 = " ^ Int.toString (!r1) ^
                " r2 = " ^ Int.toString (!r2) ^ "\n");
val () = print "SCALING_DONE\n";
