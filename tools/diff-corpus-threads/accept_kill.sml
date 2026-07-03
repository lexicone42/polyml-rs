(* Kill a thread blocked in Socket.accept (no client will ever connect):
   upstream aborts the accept promptly. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val loopback = valOf (NetHostDB.fromString "127.0.0.1");
val m = M.mutex (); val cv = C.conditionVar (); val ready = ref false;
fun acceptor () =
  let val s = INetSock.TCP.socket ()
      val () = Socket.bind (s, INetSock.toAddr (loopback, 0))
      val () = Socket.listen (s, 2)
      val () = (M.lock m; ready := true; C.signal cv; M.unlock m)
      val _ = Socket.accept s          (* blocks forever — no client *)
  in () end;
val t = T.fork (acceptor, []);
val () = (M.lock m; while not (!ready) do C.wait (cv, m); M.unlock m);
val t0 = Time.now ();
val () = (T.kill t) handle _ => ();
fun drain () = if T.isActive t andalso Time.< (Time.- (Time.now (), t0), Time.fromSeconds 15)
               then drain () else ();
val () = drain ();
val fast = Time.< (Time.- (Time.now (), t0), Time.fromSeconds 5);
val () = print ("@@killed_fast=" ^ Bool.toString fast ^ " active=" ^ Bool.toString (T.isActive t) ^ "\n");
