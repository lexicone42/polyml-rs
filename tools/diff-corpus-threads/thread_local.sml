(* Thread-local storage: each thread's slot is private and survives. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val tag : int Universal.tag = Universal.tag ();
val m = M.mutex (); val cv = C.conditionVar ();
val done_n = ref 0; val seen = ref 0;
fun worker k () =
  (T.setLocal (tag, k * 100);
   let fun spin 0 = () | spin n = spin (n - 1) in spin 20000 end;
   let val v = T.getLocal tag
   in M.lock m;
      seen := !seen + (case v of SOME x => x | NONE => ~1);
      done_n := !done_n + 1; C.signal cv; M.unlock m
   end);
val () = ignore (T.fork (worker 1, []));
val () = ignore (T.fork (worker 2, []));
val () = ignore (T.fork (worker 3, []));
val () = (M.lock m; while !done_n < 3 do C.wait (cv, m); M.unlock m);
val main_slot = T.getLocal tag;
val () = print ("@@seen=" ^ Int.toString (!seen) ^ " main=" ^
                (case main_slot of NONE => "none" | SOME _ => "some") ^ "\n");
