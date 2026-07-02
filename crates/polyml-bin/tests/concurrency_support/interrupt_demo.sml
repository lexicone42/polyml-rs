(* Thread-attribute interrupt fidelity (concurrency increment).

   Exercises the upstream InterruptState semantics end-to-end through the
   real basis Thread structure:

   1. ASYNC:    `Thread.interrupt` on a compute-bound worker forked with
                InterruptState=InterruptAsynch raises SML `Interrupt` in
                the worker at a safepoint (ProcessAsynchRequests).
   2. CONDVAR:  `Thread.interrupt` on a worker blocked in
                `ConditionVar.wait` wakes it; the basis' innerWait calls
                testInterrupt, which delivers the (Synch-state) interrupt
                — how an interrupt cancels a wait (WaitInfinite +
                TestSynchronousRequests).
   3. DEFER:    a worker forked with InterruptState=InterruptDefer does
                NOT receive a pending interrupt — not at safepoints, not
                even via an explicit testInterrupt — until it flips its
                state to InterruptSynch, whereupon testInterrupt raises.

   Each phase prints a *_OK / *_FAIL marker the Rust test asserts on.  *)

structure T = Thread.Thread;
structure M = Thread.Mutex;
structure C = Thread.ConditionVar;

val m = M.mutex ();  (* protects every shared flag below *)

fun getFlag (r : bool ref) = (M.lock m; !r before M.unlock m);
fun setFlag (r : bool ref) = (M.lock m; r := true; M.unlock m);
fun waitFlag r = if getFlag r then () else waitFlag r;

(* Pure local computation (crosses many safepoints). *)
fun spin (acc, 0) = acc
  | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);

(* ---- 1. Asynchronous delivery to a compute-bound loop. ---------- *)
local
  val started = ref false and got = ref false and ranOut = ref false
  (* Bounded busy loop: if delivery is broken we report a FAIL marker
     instead of hanging to the step cap. *)
  fun busy 0 = ()
    | busy n = (ignore (spin (n, 100)); busy (n - 1))
  val w = T.fork (fn () =>
      ((setFlag started; busy 100000; setFlag ranOut)
         handle T.Interrupt => setFlag got),
    [T.InterruptState T.InterruptAsynch])
in
  val () = waitFlag started;          (* handler is provably installed *)
  val () = T.interrupt w;
  fun w1 () = if getFlag got orelse getFlag ranOut then () else w1 ();
  val () = w1 ();
  val () = if getFlag got andalso not (getFlag ranOut)
           then print "INTERRUPT_ASYNC_OK\n"
           else print "INTERRUPT_ASYNC_FAIL\n"
end;

(* ---- 2. Interrupt cancels a ConditionVar.wait. ------------------ *)
local
  val cvm = M.mutex ()
  val cv = C.conditionVar ()
  val inwait = ref false and got = ref false
  val w = T.fork (fn () =>
      (M.lock cvm;
       setFlag inwait;
       (C.wait (cv, cvm); M.unlock cvm)   (* never signalled *)
         handle T.Interrupt => setFlag got),
    [])
in
  val () = waitFlag inwait;
  val () = T.interrupt w;
  val () = waitFlag got;
  val () = print "INTERRUPT_CONDVAR_OK\n"
end;

(* ---- 3. InterruptDefer really defers. --------------------------- *)
local
  val started = ref false and sent = ref false
  val deferHeld = ref false and got = ref false and leaked = ref false
  val w = T.fork (fn () =>
      ((setFlag started;
        waitFlag sent;
        (* The interrupt is pending NOW (main sent it before `sent`).
           Burn well past a safepoint boundary: under Defer nothing may
           be delivered there... *)
        ignore (spin (1, 200000));
        (* ...nor even at an explicit interruption point (upstream:
           TestSynchronousRequests delivers only Synch,
           ProcessAsynchRequests only Asynch — Defer leaves it pending). *)
        T.testInterrupt ();
        setFlag deferHeld;
        (* Flip to Synch and collect the deferred interrupt. *)
        T.setAttributes [T.InterruptState T.InterruptSynch];
        T.testInterrupt ();
        setFlag leaked)                   (* NOT reached if it raises *)
         handle T.Interrupt => setFlag got),
    [T.InterruptState T.InterruptDefer])
in
  val () = waitFlag started;
  val () = T.interrupt w;                 (* pending, deferred... *)
  val () = setFlag sent;                  (* ...before the worker proceeds *)
  fun w3 () = if getFlag got orelse getFlag leaked then () else w3 ();
  val () = w3 ();
  val () = if getFlag got andalso getFlag deferHeld
              andalso not (getFlag leaked)
           then print "DEFER_OK\n"
           else print "DEFER_FAIL\n"
end;

val () = print "INTERRUPT_DEMO_DONE\n";
