(* Fork-heavy allocation storm (P2b fence) — many GC cycles with live data
   flowing between threads while workers allocate hard.

   Three workers each build and fold lists (heavy allocation), depositing
   their running totals into a shared mutex-protected accumulator; main
   spins until every worker reports done, then checks the exact total.
   Under a LOW GC threshold this forces many collections whose roots span
   every thread's stack + the shared accumulator — with per-thread
   nurseries (P2b) each collection must promote every worker's live data
   into the primary and reset the worker nurseries, without losing or
   corrupting a single cons cell.

   The EXACT-TOTAL check is the discriminator: a dropped or double-promoted
   object shows up as a wrong sum (or a crash), not a flaky timing. *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

val () =
let
  val m = M.mutex ()
  val total = ref 0
  val doneCount = ref 0
  fun withLock f = (M.lock m; let val v = f () in M.unlock m; v end)

  val rounds = 60
  val listLen = 4000

  (* One worker: `rounds` iterations of build-a-list / fold-it / deposit. *)
  fun worker () =
    let
      fun build 0 acc = acc
        | build n acc = build (n - 1) (n :: acc)
      fun round r =
        if r = 0 then ()
        else
          let
            val l = build listLen []
            val s = List.foldl (op +) 0 l
          in
            withLock (fn () => total := !total + s);
            round (r - 1)
          end
    in
      round rounds;
      withLock (fn () => doneCount := !doneCount + 1)
    end

  val _ = T.fork (worker, [])
  val _ = T.fork (worker, [])
  val _ = T.fork (worker, [])

  fun join () = if withLock (fn () => !doneCount) >= 3 then () else join ()
  val () = join ()

  (* Each round deposits sum(1..listLen) = listLen*(listLen+1)/2. *)
  val perRound = listLen * (listLen + 1) div 2
  val expected = 3 * rounds * perRound
  val got = withLock (fn () => !total)
in
  print ("TOTAL=" ^ Int.toString got ^ " EXPECTED=" ^ Int.toString expected ^ "\n");
  print (if got = expected then "ALLOC_STORM_PASS\n" else "ALLOC_STORM_FAIL\n")
end;
