(* Wave 1b socket demo: a single-threaded TCP ECHO SERVER driven through the
   self-bootstrapped `polyexport` REPL, exercising the REAL `PolyNetwork*`
   RTS entry points (create/bind/listen/getsockname/accept/recv/send/close).

   Flow (all on ONE mutator thread, blocking sockets):
     1. create a TCP socket, bind it to 127.0.0.1:0 (an ephemeral port),
     2. listen, then read back the kernel-assigned port via getsockname,
     3. print "PORT=<n>" and FLUSH it (the Rust harness reads this line, then
        connects a std::net client to that port),
     4. accept ONE connection (blocks the single mutator until the client
        arrives — correct under the default single-threaded model),
     5. recv the client's bytes and send them straight back (echo),
     6. print "ECHOED=<n>" and close both sockets.

   The companion `tests/sockets.rs` is the CLIENT: it reads PORT, connects,
   sends a payload, and asserts the identical bytes come back — proving bytes
   round-trip through real kernel sockets. *)
val () =
let
  val srv = INetSock.TCP.socket ()
  val () = Socket.bind (srv, INetSock.any 0)
  val () = Socket.listen (srv, 5)
  (* getsockname -> the ephemeral port the kernel chose. *)
  val (_, port) = INetSock.fromAddr (Socket.Ctl.getSockName srv)
  val () = print ("PORT=" ^ Int.toString port ^ "\n")
  val () = TextIO.flushOut TextIO.stdOut
  (* Blocking accept: waits for the Rust client to connect. *)
  val (conn, _) = Socket.accept srv
  (* Echo: one recv (up to 4096 bytes) straight back out. *)
  val msg = Socket.recvVec (conn, 4096)
  val n = Socket.sendVec (conn, Word8VectorSlice.full msg)
  val () = print ("ECHOED=" ^ Int.toString n ^ "\n")
  val () = TextIO.flushOut TextIO.stdOut
  val () = Socket.close conn
  val () = Socket.close srv
in () end;
