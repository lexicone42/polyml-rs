(* RACY-REF probe (P4): two threads hammer ONE shared ref with NO mutex.

   This is deliberately racy SML. The fence is about the RUNTIME, not
   the program: under POLY_PARALLEL=1 both threads really execute at
   once, so increments WILL be lost — that is the program's bug, and
   any final value in (0, 2*iters] is acceptable. What must NOT happen
   is a runtime-level failure: a crash, a GC invariant violation, or a
   value outside the bounds any interleaving of word-atomic reads and
   writes could produce (each `!v` / `v := _` is a single relaxed-atomic
   word access under the Position-2 memory model — racy programs get
   unspecified VALUES, never undefined BEHAVIOR).

   Completion is signalled under a real mutex + condvar so the join
   itself is sound.                                                     *)

structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;

val iters = 200000;

val v = ref 0;                  (* the deliberately-unprotected target *)

val m  = M.mutex ();
val cv = C.conditionVar ();
val nDone = ref 0;

fun hammer () =
  let
    fun go 0 = ()
      | go n = (v := !v + 1; go (n - 1))
  in
    go iters;
    M.lock m; nDone := !nDone + 1; C.signal cv; M.unlock m
  end;

val () = ignore (T.fork (hammer, []));
val () = ignore (T.fork (hammer, []));
val () = (M.lock m;
          while !nDone < 2 do C.wait (cv, m);
          M.unlock m);

val final = !v;
val () = print ("racy final = " ^ Int.toString final ^
                " (max " ^ Int.toString (2 * iters) ^ ")\n");
val () =
  if final > 0 andalso final <= 2 * iters
  then print "RACY_REF_OK\n"
  else print "RACY_REF_BAD\n";
