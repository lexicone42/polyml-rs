(* Mutex-hammer (P3 atomics fence) — two threads contend the SAME mutex on
   a tight loop, each doing many lock/incr/unlock cycles on a shared ref.

   This directly exercises the atomic mutex-word opcodes (lockMutex /
   tryLockMutex / atomicReset) under real contention: if the lock/unlock
   were a plain read-modify-write (the pre-P3 TOCTOU), two threads could
   both observe the mutex unlocked and both enter the critical section,
   dropping increments — visible as counter < 2*N.

   The EXACT count is the discriminator (2*N, no more, no less). Under the
   giant lock this already held (one mutator at a time); the atomic ops
   keep it correct as the lock is broken. *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

val () =
let
  val n = 200000
  val m  = M.mutex ()
  val dm = M.mutex ()
  val counter = ref 0
  val done = ref 0

  fun worker () =
    let
      fun loop 0 = ()
        | loop k = (M.lock m; counter := !counter + 1; M.unlock m; loop (k - 1))
    in
      loop n;
      M.lock dm; done := !done + 1; M.unlock dm
    end

  val _ = T.fork (worker, [])
  val _ = T.fork (worker, [])

  fun joinAll () =
    if (M.lock dm; let val d = !done in M.unlock dm; d end) >= 2
    then () else joinAll ()
  val () = joinAll ()

  val got = !counter
  val expected = 2 * n
in
  print ("COUNTER=" ^ Int.toString got ^ " EXPECTED=" ^ Int.toString expected ^ "\n");
  print (if got = expected then "MUTEX_HAMMER_PASS\n" else "MUTEX_HAMMER_FAIL\n")
end;
