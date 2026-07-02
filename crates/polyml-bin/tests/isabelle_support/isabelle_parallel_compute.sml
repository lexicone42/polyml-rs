(* Isabelle's OWN futures scheduler (Concurrent/future.ML, Par_List) running
   on the polyml-rs runtime — pure-compute scaling probe.

   Par_List.map forks one future per item; Isabelle's scheduler thread
   spawns worker threads up to max_threads (= numProcessors via
   max_threads_update 0). Under POLY_PARALLEL=1 those workers run on real
   cores. The spin results are deterministic — the harness asserts the
   giant-lock run and the parallel run print IDENTICAL result lines.     *)

val () = restore_pure_context ();
val () = Multithreading.max_threads_update 0;
val () = writeln ("max_threads = " ^ Int.toString (Multithreading.max_threads ()));

fun spin (acc, 0) = acc
  | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);

val t0 = Time.now ();
val rs = Par_List.map (fn s => spin (s, 30000000)) [1, 2, 3, 4];
val t1 = Time.now ();
val () = writeln ("PAR_RESULTS = " ^ String.concatWith "," (map Int.toString rs));
val () = writeln ("ELAPSED_MS = " ^ LargeInt.toString (Time.toMilliseconds (t1 - t0)));
val () = writeln "SCALE_PROBE_DONE";
