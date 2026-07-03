structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;
val rb = ref (Word8Array.array (1, 0w0));
val m = M.mutex (); val cv = C.conditionVar (); val nDone = ref 0;
fun publisher 0 = () | publisher n =
  (rb := Word8Array.array (8, Word8.fromInt (n mod 256)); publisher (n - 1));
fun consumer (0, s) = s
  | consumer (n, s) =
      let val a = !rb
          val x = (Word8.toInt (Word8Array.sub (a, 0)) handle _ => 0)
      in consumer (n - 1, s + x) end;
fun finish () = (M.lock m; nDone := !nDone + 1; C.signal cv; M.unlock m);
val () = ignore (T.fork (fn () => (publisher 30000; finish ()), []));
val () = ignore (T.fork (fn () => (ignore (consumer (30000, 0)); finish ()), []));
val () = (M.lock m; while !nDone < 2 do C.wait (cv, m); M.unlock m);
val () = print "BYTE_PROBE_DONE\n";
