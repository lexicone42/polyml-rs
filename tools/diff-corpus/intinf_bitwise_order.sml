(* diff-corpus: IntInf bitwise both-arg-orders (closes the andb/orb arg-order gap;
   the optimizer special-case for andb/orb drops the isShort j guard — task #72). *)
val () = print ("@@andb_negsmall_big=" ^ IntInf.toString (IntInf.andb(~1, IntInf.pow(2,80))) ^ "\n");
val () = print ("@@andb_big_negsmall=" ^ IntInf.toString (IntInf.andb(IntInf.pow(2,80), ~1)) ^ "\n");
val () = print ("@@andb_neg2_big=" ^ IntInf.toString (IntInf.andb(~2, IntInf.pow(2,80))) ^ "\n");
val () = print ("@@orb_possmall_big=" ^ IntInf.toString (IntInf.orb(5, IntInf.pow(2,80))) ^ "\n");
val () = print ("@@orb_big_possmall=" ^ IntInf.toString (IntInf.orb(IntInf.pow(2,80), 5)) ^ "\n");
val () = print ("@@orb_negsmall_big=" ^ IntInf.toString (IntInf.orb(~2, IntInf.pow(2,80))) ^ "\n");
val () = print ("@@xorb_possmall_big=" ^ IntInf.toString (IntInf.xorb(5, IntInf.pow(2,80))) ^ "\n");
val () = print ("@@xorb_big_possmall=" ^ IntInf.toString (IntInf.xorb(IntInf.pow(2,80), 5)) ^ "\n");
val () = print ("@@andb_possmall_big=" ^ IntInf.toString (IntInf.andb(7, IntInf.pow(2,80) + 15)) ^ "\n");
