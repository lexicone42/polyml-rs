val () = restore_pure_context ();
val () = Multithreading.max_threads_update 0;
val () = Proofterm.proofs := 0;
val () = writeln ("max_threads = " ^ Int.toString (Multithreading.max_threads ()));

(* One task = real LCF kernel throughput: 100,000 certified inferences
   (symmetric + transitive per iteration) on this task's own Free variable.
   Each worker restores the Pure context into ITS OWN Thread_Data slot —
   thread-local by construction, no sharing. *)
fun kernel_task seed =
  let
    val () = Context.put_generic_context (SOME Pure_context);
    val thy = Context.the_global_context ();
    val x = Free ("x" ^ Int.toString seed, TFree ("'a", []));
    val ct = Thm.global_cterm_of thy x;
    fun iter (th, 0) = th
      | iter (th, k) = iter (Thm.transitive th (Thm.symmetric th), k - 1);
    val th = iter (Thm.reflexive ct, 50000);
    val (lhs, rhs) = Logic.dest_equals (Thm.prop_of th);
    val sound =
      null (Thm.hyps_of th) andalso lhs aconv x andalso rhs aconv x;
  in if sound then 1 else 0 end;

val t0 = Time.now ();
val oks = Par_List.map kernel_task [1, 2, 3, 4, 5, 6];
val t1 = Time.now ();
val () = writeln ("SOUND_TASKS = " ^ Int.toString (List.foldl (op +) 0 oks) ^ "/6");
val () = writeln ("ELAPSED_MS = " ^ LargeInt.toString (Time.toMilliseconds (t1 - t0)));
val () = writeln "KERNEL_PAR_DONE";
