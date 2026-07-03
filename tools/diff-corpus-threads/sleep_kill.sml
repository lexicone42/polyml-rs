(* Kill a thread blocked in OS.Process.sleep: upstream wakes+kills it
   promptly. Deterministic: we print whether death happened well before
   the sleep could expire. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar (); val ready = ref false;
fun sleeper () = (M.lock m; ready := true; C.signal cv; M.unlock m;
                  OS.Process.sleep (Time.fromSeconds 30));
val t = T.fork (sleeper, []);
val () = (M.lock m; while not (!ready) do C.wait (cv, m); M.unlock m);
val t0 = Time.now ();
val () = (T.kill t) handle _ => ();
fun drain () = if T.isActive t andalso Time.< (Time.- (Time.now (), t0), Time.fromSeconds 20)
               then drain () else ();
val () = drain ();
val fast = Time.< (Time.- (Time.now (), t0), Time.fromSeconds 5);
val () = print ("@@killed_fast=" ^ Bool.toString fast ^ " active=" ^ Bool.toString (T.isActive t) ^ "\n");
