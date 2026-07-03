(* Exact Mutex.trylock semantics, single thread — deterministic booleans. *)
structure M = Thread.Mutex;
val m = M.mutex ();
val a = M.trylock m;          (* free -> true *)
val b = M.trylock m;          (* held (by self) -> false, non-recursive *)
val () = M.unlock m;
val c = M.trylock m;          (* free again -> true *)
val () = M.unlock m;
val () = print ("@@" ^ Bool.toString a ^ "," ^ Bool.toString b ^ "," ^ Bool.toString c ^ "\n");
