(* Preemption-fairness proof (concurrency: thread-attribute increment).

   At the interpreter level, "preemption" is the safepoint cooperative
   yield (every 65536 steps, `cooperative_yield` in interpreter/mod.rs):
   a COMPUTE-BOUND thread that never blocks must still hand the giant
   lock to a waiting peer. This driver proves that hand-off actually
   interleaves compute-bound threads fairly:

   - Fork TWO workers whose hot loop is PURE local computation (no
     mutex, no blocking call — nothing that would release the lock
     voluntarily). Each bumps a shared progress ref only once per
     50_000-iteration round, under a mutex.
   - The main thread samples both counters. At the FIRST sample where
     the combined progress crosses a quarter of the total, BOTH must be
     strictly between 0 and done: if scheduling were run-to-completion
     (no interleaving), that first sample would show one worker at the
     threshold and the other still at 0.
   - Then join both and check the final totals.

   NB fork + sample + join are ONE top-level declaration: the REPL only
   compiles the next declaration after the current one finishes, so a
   multi-declaration version would let the workers run to completion
   while the sampler was still being compiled.                       *)

structure T = Thread.Thread;
structure M = Thread.Mutex;

val rounds = 40;          (* progress bumps per worker *)
val spinPerRound = 50000; (* pure-compute iterations between bumps *)

val m  = M.mutex ();
val p1 = ref 0 and p2 = ref 0;

(* Pure local computation: no allocation beyond tagged ints, no locks. *)
fun spin (acc, 0) = acc
  | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);

fun worker p =
  let
    fun go 0 = ()
      | go r =
          (ignore (spin (r, spinPerRound));
           M.lock m; p := !p + 1; M.unlock m;
           go (r - 1))
  in go rounds end;

val (a, b, fa, fb) =
  let
    val _ = T.fork (fn () => worker p1, [])
    val _ = T.fork (fn () => worker p2, [])
    (* Sample until combined progress crosses total/4; snapshot both. *)
    fun sample () =
      let
        val (a, b) = (M.lock m; (!p1, !p2) before M.unlock m)
      in
        if a + b >= rounds div 2 then (a, b) else sample ()
      end
    val (a, b) = sample ()
    (* Join: wait for both to finish. *)
    fun join () =
      let val (x, y) = (M.lock m; (!p1, !p2) before M.unlock m)
      in if x >= rounds andalso y >= rounds then (x, y) else join () end
    val (fa, fb) = join ()
  in (a, b, fa, fb) end;

val () = print ("midway: p1 = " ^ Int.toString a ^
                " p2 = " ^ Int.toString b ^ "\n");
val () =
  if a > 0 andalso b > 0 andalso a < rounds andalso b < rounds
  then print "PREEMPT_OK\n"
  else print "PREEMPT_FAIL\n";

val () = print ("final: p1 = " ^ Int.toString fa ^
                " p2 = " ^ Int.toString fb ^ "\n");
val () =
  if fa = rounds andalso fb = rounds
  then print "FINAL_OK\n"
  else print "FINAL_FAIL\n";
