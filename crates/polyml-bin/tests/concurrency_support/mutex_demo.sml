(* Two-thread mutex demo (concurrency increment 3, Track A).

   One Mutex + a shared (ref 0). Fork 2 threads, each doing N iterations
   of { lock; r := !r + 1; unlock }. Wait for both to finish, then assert
   !r = 2N. A PASS proves real mutual exclusion + real fork + real
   interleaving under the giant lock.

   Join is done by a shared `done` counter (also mutex-protected): each
   child bumps it on completion; the parent spin-waits (its safepoint
   yields the giant lock so children run). *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

val n = 100000;

val m   = M.mutex ();      (* protects `counter` *)
val dm  = M.mutex ();      (* protects `done`    *)
val counter = ref 0;
val done    = ref 0;

fun worker () =
  let
    fun loop 0 = ()
      | loop k =
          (M.lock m; counter := !counter + 1; M.unlock m; loop (k - 1))
  in
    loop n;
    M.lock dm; done := !done + 1; M.unlock dm
  end;

val _ = T.fork (worker, []);
val _ = T.fork (worker, []);

(* Spin-wait for both children. Reading `done` under its mutex; the loop
   body allocates / steps enough that the interpreter's safepoint yields
   the giant lock to the children. *)
fun joinAll () =
  let
    val d = (M.lock dm; let val v = !done in M.unlock dm; v end)
  in
    if d >= 2 then () else joinAll ()
  end;

val () = joinAll ();

val result = !counter;
val expected = 2 * n;
val () = print ("counter = " ^ Int.toString result ^
                " expected = " ^ Int.toString expected ^
                (if result = expected then "  PASS\n" else "  FAIL\n"));
