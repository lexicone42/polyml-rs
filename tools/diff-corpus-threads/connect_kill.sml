(* Kill a thread blocked in Socket.connect to a non-routable address
   (10.255.255.1:80 — SYN retries for minutes): upstream aborts promptly. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val target = valOf (NetHostDB.fromString "10.255.255.1");
val m = M.mutex (); val cv = C.conditionVar (); val ready = ref false;
fun connector () =
  let val s : (INetSock.inet, Socket.active Socket.stream) Socket.sock = INetSock.TCP.socket ()
      val () = (M.lock m; ready := true; C.signal cv; M.unlock m)
  in (Socket.connect (s, INetSock.toAddr (target, 80))) handle _ => () end;
val t = T.fork (connector, []);
val () = (M.lock m; while not (!ready) do C.wait (cv, m); M.unlock m);
val () = OS.Process.sleep (Time.fromMilliseconds 300); (* let it enter connect *)
val t0 = Time.now ();
val () = (T.kill t) handle _ => ();
fun drain () = if T.isActive t andalso Time.< (Time.- (Time.now (), t0), Time.fromSeconds 15)
               then drain () else ();
val () = drain ();
val fast = Time.< (Time.- (Time.now (), t0), Time.fromSeconds 5);
val () = print ("@@killed_fast=" ^ Bool.toString fast ^ " active=" ^ Bool.toString (T.isActive t) ^ "\n");
