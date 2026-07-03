(* Interrupt a thread blocked in OS.Process.sleep (InterruptAsynch): the
   Interrupt exception must land promptly, caught by the sleeper's own
   handler. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar ();
val ready = ref false; val caught = ref false; val done_f = ref false;
fun sleeper () =
  ((M.lock m; ready := true; C.signal cv; M.unlock m;
    OS.Process.sleep (Time.fromSeconds 30))
   handle T.Interrupt => (M.lock m; caught := true; done_f := true; C.signal cv; M.unlock m));
val t = T.fork (sleeper, [T.InterruptState T.InterruptAsynch]);
val () = (M.lock m; while not (!ready) do C.wait (cv, m); M.unlock m);
val t0 = Time.now ();
val () = (T.interrupt t) handle _ => ();
val () = (M.lock m;
          while not (!done_f) andalso Time.< (Time.- (Time.now (), t0), Time.fromSeconds 20)
          do ignore (C.waitUntil (cv, m, Time.+ (Time.now (), Time.fromMilliseconds 200)));
          M.unlock m);
val fast = Time.< (Time.- (Time.now (), t0), Time.fromSeconds 5);
val () = print ("@@caught=" ^ Bool.toString (!caught) ^ " fast=" ^ Bool.toString fast ^ "\n");
