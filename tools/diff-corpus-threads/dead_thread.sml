(* A thread that raises an uncaught exception just dies; isActive goes
   false; the process continues deterministically. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar (); val flag = ref false;
fun dier () = (M.lock m; flag := true; C.signal cv; M.unlock m; raise Fail "expected-death");
val t = T.fork (dier, []);
val () = (M.lock m; while not (!flag) do C.wait (cv, m); M.unlock m);
fun drain 0 = () | drain n = if T.isActive t then drain (n - 1) else ();
val () = drain 100000000;
val () = print ("@@active=" ^ Bool.toString (T.isActive t) ^ " alive_main=true\n");
