(* Parked-stdin demo — proves a thread blocked reading STDIN releases the
   giant lock (and that a GC while it is parked is sound).

   Main forks a WORKER that loops forever: allocate garbage (under a low
   POLYML_GC_THRESHOLD collections fire constantly) and bump a
   mutex-protected counter. The protocol with the Rust harness is
   two-phase, because the REPL and the program SHARE the buffered stdin
   stream (leftovers from the driver text itself — e.g. its trailing
   newline — are still in the buffer, so a single naive read returns
   instantly):

     1. main prints READY, then reads lines until it sees "mark" (this
        consumes any buffered leftovers; the harness sends "mark"
        immediately, so none of these reads block for long);
     2. snapshot p0, print MARKED, then read the NEXT line — the harness
        sleeps ~2s before sending it, so THIS read genuinely blocks;
     3. snapshot p1 and report the delta.

   Discrimination: while main is blocked in the kernel read it hits NO
   safepoints, so if the read HELD the giant lock the worker would make
   exactly ZERO progress in the p1-p0 window (verified empirically — a
   non-parking read yields delta = 0). A parked read frees the worker for
   the whole ~2s → delta in the thousands. The go-line is long, so its
   intact round-trip also exercises the bounce+forwarded-cell copy after
   the collector has moved the destination buffer many times.

   Single declaration — the REPL compiles one declaration at a time, so
   everything timing-sensitive stays in one. *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

val () =
let
  val m = M.mutex ()
  val progress = ref 0
  val stop = ref false
  fun withLock f = (M.lock m; let val v = f () in M.unlock m; v end)
  (* Allocation-heavy worker: builds + discards a list each round, so the
     collector runs constantly while main is parked in the stdin read.
     Checks `stop` each round — an immortal worker would hang the REPL's
     exit (wait_for_children waits for non-daemon threads). *)
  fun worker () =
    let
      fun burn 0 acc = List.length acc
        | burn n acc = burn (n - 1) (n :: acc)
      fun loop () =
        if withLock (fn () => !stop) then ()
        else (ignore (burn 2000 []); withLock (fn () => progress := !progress + 1); loop ())
    in
      loop ()
    end
  fun chomp s = String.substring (s, 0, size s - 1)  (* drop trailing \n *)
  fun readLine () = case TextIO.inputLine TextIO.stdIn of SOME s => s | NONE => "<eof>\n"
  (* Phase 1: consume buffered leftovers until the harness's "mark". *)
  fun awaitMark () = if chomp (readLine ()) = "mark" then () else awaitMark ()
  val _ = T.fork (worker, [])
  val () = print "READY\n"
  val () = TextIO.flushOut TextIO.stdOut
  val () = awaitMark ()
  val p0 = withLock (fn () => !progress)
  val () = print "MARKED\n"
  val () = TextIO.flushOut TextIO.stdOut
  (* Phase 2: THIS read blocks (~2s) — the parked window. *)
  val goLine = chomp (readLine ())
  val p1 = withLock (fn () => !progress)
  val () = withLock (fn () => stop := true)   (* let the worker exit *)
in
  print ("GOT=[" ^ goLine ^ "]\n");
  print ("DELTA=" ^ Int.toString (p1 - p0) ^ "\n");
  print (if p1 - p0 > 10 then "STDIN_PARK_PASS\n" else "STDIN_PARK_FAIL\n")
end;
