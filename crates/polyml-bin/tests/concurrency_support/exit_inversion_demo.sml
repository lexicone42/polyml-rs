(* PolyFinish exit-semantics demo (P0) — a forked thread calling
   OS.Process.exit must terminate the PROCESS, not be silently swallowed
   while the program keeps running.

   THE INVERSION (fixed): the process-exit flag used to be consumed by
   whichever thread stepped next. A child's OS.Process.exit ended only the
   CHILD's run loop (an ordinary thread exit) while the main program ran on
   — exit inverted into a no-op-for-the-caller. Now the exiting thread
   broadcasts KILL to every peer and leaves the flag set, so the whole
   process winds down.

   Main forks a worker that exits almost immediately, then does a large
   amount of work whose completion would print BUG_REACHED_END. A correct
   process never prints it: the worker's exit stops main at its next
   safepoint. (The exact status code is not asserted here — the interactive
   REPL's own top-level mediates it; the load-bearing property is that the
   exit is NOT swallowed.) *)

structure T = Thread.Thread;

val () = print "BEGIN\n";
val () = TextIO.flushOut TextIO.stdOut;

val _ = T.fork (fn () => OS.Process.exit (Word8.fromInt 3), []);

(* Busy work long enough that, absent a working process-exit, main would
   certainly reach the end and print the bug marker. *)
fun spin (n, acc) = if n = 0 then acc else spin (n - 1, (acc + n) mod 1000000);
val r = spin (500000000, 0);

val () = print ("BUG_REACHED_END r=" ^ Int.toString r ^ "\n");
