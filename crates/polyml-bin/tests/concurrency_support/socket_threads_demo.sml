(* In-process concurrent socket demo — the definitive accept-park test.

   A forked SERVER thread binds/listens on the loopback address, publishes
   its kernel-assigned port to a mutex-protected ref, then BLOCKS in accept.
   The MAIN thread (the client) waits for the port, connects to the same
   loopback address, sends a payload, and reads the echo back.

   WHY THIS PROVES ACCEPT-PARKING: with one mutator at a time under the
   giant lock, if the server's blocking `accept` held the lock, the main
   thread could never run to connect — a deadlock, with neither side making
   progress. It completes ONLY because `accept` (and `connect`) release the
   giant lock across their wait (`park_while_blocking`), so the two threads
   hand off. A regression that stopped parking accept turns this into a
   hang. *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

(* Loopback address, shared by both ends. `fromString` parses the literal
   with no DNS (getByName would need the stubbed getAddrInfo). *)
val loopback = valOf (NetHostDB.fromString "127.0.0.1");

val m = M.mutex ();            (* protects `port` and `serverDone` *)
val port = ref ~1;            (* server publishes its port here; ~1 = not yet *)
val serverDone = ref false;

fun withLock f = (M.lock m; let val v = f () in M.unlock m; v end);

val payload = "PING-through-the-giant-lock";

fun server () =
  let
    val s = INetSock.TCP.socket ()
    (* No setREUSEADDR — Socket.Ctl.setOption is still a stub, and an
       ephemeral (port 0) bind doesn't need it. *)
    val () = Socket.bind (s, INetSock.toAddr (loopback, 0))
    val () = Socket.listen (s, 5)
    val (_, p) = INetSock.fromAddr (Socket.Ctl.getSockName s)
    val () = withLock (fn () => port := p)          (* publish the port *)
    val (conn, _) = Socket.accept s                 (* BLOCKS — must release the lock *)
    val got = Socket.recvVec (conn, 4096)
    val _ = Socket.sendVec (conn, Word8VectorSlice.full got)  (* echo *)
    val () = Socket.close conn
    val () = Socket.close s
    val () = withLock (fn () => serverDone := true)
  in () end;

val _ = T.fork (server, []);

(* Client (main thread): wait for the server's port, then connect + echo. *)
fun awaitPort () =
  case withLock (fn () => !port) of
      ~1 => awaitPort ()
    | p  => p;

val p = awaitPort ();
(* Annotate the client socket ACTIVE so the value restriction doesn't freeze
   its mode to a dummy monotype before connect/sendVec constrain it. *)
val c : (INetSock.inet, Socket.active Socket.stream) Socket.sock =
  INetSock.TCP.socket ();
val () = Socket.connect (c, INetSock.toAddr (loopback, p));
val _ = Socket.sendVec (c, Word8VectorSlice.full (Byte.stringToBytes payload));
val echoed = Socket.recvVec (c, 4096);
val () = Socket.close c;

val got = Byte.bytesToString echoed;
val ok = (got = payload) andalso withLock (fn () => !serverDone);
val () = print ("ECHO=[" ^ got ^ "]\n");
val () = print (if ok then "SOCKET_THREADS_PASS\n" else "SOCKET_THREADS_FAIL\n");
