(* Strict alternation via a turn variable: the interleaving is FORCED,
   so the accumulated sequence checksum is deterministic. *)
structure T = Thread.Thread; structure M = Thread.Mutex; structure C = Thread.ConditionVar;
val m = M.mutex (); val cv = C.conditionVar ();
val turn = ref 0; val acc = ref 0; val rounds = 2000;
fun player (me, mul) () =
  let fun go 0 = () | go n =
        (M.lock m;
         while !turn <> me do C.wait (cv, m);
         acc := !acc * mul + me;
         turn := 1 - me; C.broadcast cv; M.unlock m;
         go (n - 1))
  in go rounds end;
val () = ignore (T.fork (player (0, 3), []));
val () = (player (1, 5) ());
val () = print ("@@acc=" ^ Int.toString (!acc mod 1000003) ^ "\n");
