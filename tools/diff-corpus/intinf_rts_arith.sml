(* diff-corpus category: intinf_rts_arith (2026-06-17)
   Exercises the RTS arbitrary-precision arithmetic emulation path
   (Poly{Add,Subtract,Multiply,Divide,Remainder}Arbitrary), NOT the inline
   bytecode opcodes. The `I` helper (ref-force) defeats inline specialization so
   the operation is dispatched through the RTS call. Regression fence for the
   subtraction sign bug found by upstream Tests/Succeed/Test101.ML: the RTS path
   computed arg2-arg1 (the NEGATION) instead of arg1-arg2. Subtraction is
   non-commutative, so BOTH operand orders are checked. *)

fun I x = let val r = ref x in !r end;
val big = IntInf.pow (2, 100);     (* boxed bignum *)
val mid = IntInf.pow (2, 62);      (* boxed bignum just over the tagged range *)

(* --- subtraction, both orders, short-vs-boxed and boxed-vs-boxed --- *)
val () = print ("@@sub_short_minus_big=" ^ IntInf.toString (I 0 - mid) ^ "\n");
val () = print ("@@sub_short5_minus_big=" ^ IntInf.toString (I 5 - big) ^ "\n");
val () = print ("@@sub_big_minus_short=" ^ IntInf.toString (mid - I 0) ^ "\n");
val () = print ("@@sub_big_minus_short5=" ^ IntInf.toString (big - I 5) ^ "\n");
val () = print ("@@sub_big_minus_big=" ^ IntInf.toString (big - I mid) ^ "\n");
val () = print ("@@sub_neg=" ^ IntInf.toString (I (~5) - big) ^ "\n");
val () = print ("@@sub_self=" ^ IntInf.toString (I big - big) ^ "\n");

(* --- the commutative ops (must stay correct) --- *)
val () = print ("@@add_short_big=" ^ IntInf.toString (I 7 + big) ^ "\n");
val () = print ("@@add_big_short=" ^ IntInf.toString (big + I 7) ^ "\n");
val () = print ("@@mul_short_big=" ^ IntInf.toString (I 3 * big) ^ "\n");

(* --- div/rem (non-commutative; must compute arg1 OP arg2) --- *)
val () = print ("@@div_big_short=" ^ IntInf.toString (big div (I 7)) ^ "\n");
val () = print ("@@div_big_big=" ^ IntInf.toString (big div (I mid)) ^ "\n");
val () = print ("@@rem_big_short=" ^ IntInf.toString (big mod (I 7)) ^ "\n");
val () = print ("@@rem_big_big=" ^ IntInf.toString (big mod (I mid)) ^ "\n");

(* --- a longer subtraction chain (sign accumulation) --- *)
val () = print ("@@chain=" ^ IntInf.toString (((I big - mid) - big) - (I 1)) ^ "\n");
