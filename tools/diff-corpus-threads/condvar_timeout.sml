(* waitUntil with a PAST deadline must return false without blocking. *)
structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar ();
val () = M.lock m;
val past = C.waitUntil (cv, m, Time.- (Time.now (), Time.fromSeconds 5));
val soon = C.waitUntil (cv, m, Time.+ (Time.now (), Time.fromMilliseconds 50));
val () = M.unlock m;
val () = print ("@@" ^ Bool.toString past ^ "," ^ Bool.toString soon ^ "\n");
