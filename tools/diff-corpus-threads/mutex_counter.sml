(* Deterministic despite scheduling: the final count under a mutex. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar ();
val count = ref 0; val done_n = ref 0;
fun worker () =
  let fun go 0 = () | go n = (M.lock m; count := !count + 1; M.unlock m; go (n-1))
  in go 50000; M.lock m; done_n := !done_n + 1; C.signal cv; M.unlock m end;
val () = ignore (T.fork (worker, []));
val () = ignore (T.fork (worker, []));
val () = (M.lock m; while !done_n < 2 do C.wait (cv, m); M.unlock m);
val () = print ("@@count=" ^ Int.toString (!count) ^ "\n");
