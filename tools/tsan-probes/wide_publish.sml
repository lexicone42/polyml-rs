structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;
val ra = ref (Array.array (1, 0));
val rv = ref (Vector.fromList [0]);
val rs = ref "x";
val m = M.mutex (); val cv = C.conditionVar (); val nDone = ref 0;
fun publisher 0 = () | publisher n =
  (ra := Array.array (4, n);
   Array.update (!ra, n mod 4, n * 2);
   rv := Vector.fromList [n, n + 1];
   rs := Int.toString n;
   publisher (n - 1));
fun consumer (0, s) = s
  | consumer (n, s) =
      let val a = !ra val v = !rv val str = !rs
          val x = (Array.sub (a, 0) handle _ => 0)
          val y = (Vector.sub (v, 0) handle _ => 0)
          val z = String.size str
      in consumer (n - 1, s + x + y + z) end;
fun finish () = (M.lock m; nDone := !nDone + 1; C.signal cv; M.unlock m);
val () = ignore (T.fork (fn () => (publisher 50000; finish ()), []));
val () = ignore (T.fork (fn () => (ignore (consumer (50000, 0)); finish ()), []));
val () = (M.lock m; while !nDone < 2 do C.wait (cv, m); M.unlock m);
val () = print "WIDE_PROBE_DONE\n";
