(* P5 capstone — a multi-connection SML compute server under load.

   A forked ACCEPT-LOOP thread binds loopback on a kernel-assigned port,
   prints "PORT=<p>" for the external harness, then accepts nConn
   connections, forking a HANDLER thread per connection. Each handler
   reads a seed (decimal text), runs the deterministic pure-compute
   `spin` on it (the parallel-speedup payload), sends back
   "<seed>:<result>", and closes. The main thread blocks on a condvar
   until every handler has finished, then prints SERVER_DONE.

   What this exercises SIMULTANEOUSLY (the P4 integration surface):
   accept/recv/send parking, one accept-loop + nConn handler threads +
   main all live at once, handler compute that under POLY_PARALLEL=1
   runs on as many cores as there are connections, heap allocation in
   every handler (string building) across possible GCs, and real
   external TCP clients (the harness connects from Rust).

   Everything after the definitions is ONE declaration per blocking
   phase: the REPL only compiles the next declaration once the current
   finishes, so the fork returns immediately (decl 1) and the join
   blocks (decl 2) while server + handlers do the work.              *)

structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;

val nConn = 4;
val iters = 20000000;

val loopback = valOf (NetHostDB.fromString "127.0.0.1");

fun spin (acc, 0) = acc
  | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);

val m  = M.mutex ();
val cv = C.conditionVar ();
val nDone = ref 0;

fun handler conn () =
  let
    val req  = Byte.bytesToString (Socket.recvVec (conn, 4096))
    val seed = valOf (Int.fromString req)
    val v    = spin (seed, iters)
    val resp = Int.toString seed ^ ":" ^ Int.toString v
    val _    = Socket.sendVec (conn, Word8VectorSlice.full
                                       (Byte.stringToBytes resp))
    val ()   = Socket.close conn
  in
    M.lock m; nDone := !nDone + 1; C.signal cv; M.unlock m
  end;

fun server () =
  let
    val s = INetSock.TCP.socket ()
    val () = Socket.bind (s, INetSock.toAddr (loopback, 0))
    val () = Socket.listen (s, 16)
    val (_, p) = INetSock.fromAddr (Socket.Ctl.getSockName s)
    val () = print ("PORT=" ^ Int.toString p ^ "\n")
    val () = TextIO.flushOut TextIO.stdOut
    fun loop 0 = ()
      | loop k =
          let val (conn, _) = Socket.accept s
          in ignore (T.fork (handler conn, [])); loop (k - 1) end
    val () = loop nConn
    val () = Socket.close s
  in () end;

val _ = T.fork (server, []);

(* Join: block until every handler has responded. *)
val () = (M.lock m;
          while !nDone < nConn do C.wait (cv, m);
          M.unlock m);

val () = print "SERVER_DONE\n";
