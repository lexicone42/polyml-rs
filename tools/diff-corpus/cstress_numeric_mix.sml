(* 1: andb-shape — small/big mixing via an isShort-guarded fold.
   Mimics IntInf.andb's "if isShort i andalso isShort j then word else rts".
   A wrong word-path on (small,big) truncates to 0; design so a wrong
   answer is detectably non-zero-or-zero. *)
local
  (* hand-rolled andb-shape: choose path by RunCall.isShort on BOTH args *)
  fun myband (i:IntInf.int) (j:IntInf.int) =
      if RunCall.isShort i andalso RunCall.isShort j
      then IntInf.andb (i, j)            (* short/short: fine either way *)
      else IntInf.andb (i, j)            (* mixed/long: rts path *)
  val big = IntInf.pow (2, 100) + 0xF0F0F0F0   (* a long IntInf *)
  val small = 0xFF : IntInf.int                 (* a short IntInf *)
  (* fold a list, andb-ing each against big and small alternately *)
  val xs = List.tabulate (40, fn k => IntInf.fromInt (k*k+1))
  fun step (x, acc) =
      let val a = myband x big
          val b = myband x small
      in acc + a + b end
  val total = List.foldl step 0 xs
in
  val () = print ("@@andb_mix=" ^ IntInf.toString total ^ "\n")
end;

(* 2: accumulate across the FixedInt -> IntInf boundary in a loop.
   Sum of k^2 for k in 1..200 overflows FixedInt? No (63-bit big), but
   we deliberately compute factorial-ish growth that crosses into long. *)
local
  fun loop (k, acc:IntInf.int) =
      if k > 60 then acc
      else loop (k+1, acc * IntInf.fromInt k + IntInf.fromInt (k*k))
in
  val () = print ("@@cross_accum=" ^ IntInf.toString (loop (1, 1)) ^ "\n")
end;

(* 3: conditional Word vs Int path based on size predicate.
   For each n, if it fits in a Word (< some threshold) use Word ops,
   else use IntInf. Wrong path => truncation. *)
local
  fun classify (n:IntInf.int) =
      if n < 0x10000 then
        (* Word path *)
        let val w = Word.fromInt (IntInf.toInt n)
            val r = Word.andb (w, 0wxFFFF) + Word.<< (w, 0w1)
        in IntInf.fromInt (Word.toInt r) end
      else
        (* IntInf path *)
        IntInf.andb (n, 0xFFFF) + n * 2
  val inputs = [0w0, 0w255, 0w65535, 0w65536, 0w1000000, 0w100] : word list
  val results = map (fn w => classify (IntInf.fromInt (Word.toInt w))) inputs
  val s = IntInf.toString (List.foldl op+ 0 results)
in
  val () = print ("@@word_int_path=" ^ s ^ "\n")
end;

(* 4: Real vs Int in branches — choose representation by parity, fold. *)
local
  fun pick i = if i mod 3 = 0 then Real.fromInt (i*i)
               else if i mod 3 = 1 then Real.fromInt i * 1.5
               else Real.fromInt i / 2.0
  val total = List.foldl (fn (i,acc) => acc + pick i) 0.0 (List.tabulate (50, fn i => i+1))
in
  val () = print ("@@real_int_branch=" ^ Real.fmt (StringCvt.FIX (SOME 8)) total ^ "\n")
end;

(* 5: bit ops vs arithmetic chosen by isShort on a running IntInf accumulator. *)
local
  fun step (k, acc:IntInf.int) =
      let val v = IntInf.fromInt k * IntInf.pow (2, 30)  (* push toward long *)
      in
        if RunCall.isShort acc
        then acc + v                          (* arithmetic while short *)
        else IntInf.orb (acc, IntInf.andb (v, 0xFFFFFFFF))  (* bit ops once long *)
      end
  val r = List.foldl step 0 (List.tabulate (30, fn k => k+1))
in
  val () = print ("@@isshort_switch=" ^ IntInf.toString r ^ "\n")
end;

(* 6: IntInf shift/and chain guarded by isShort — andb-shape inside a loop. *)
local
  fun mask (i:IntInf.int) (j:IntInf.int) =
      if RunCall.isShort i andalso RunCall.isShort j
      then IntInf.andb (i, j)
      else IntInf.andb (IntInf.<< (i, 0w0), j)   (* identity shift then andb *)
  val big = IntInf.<< (1, 0w80) - 1              (* 80 one-bits, long *)
  val xs = List.tabulate (32, fn k => IntInf.fromInt (k*7+3))
  val r = List.foldl (fn (x,acc) => acc + mask x big + mask x 0x3FF) 0 xs
in
  val () = print ("@@mask_loop=" ^ IntInf.toString r ^ "\n")
end;

(* 7: nested case with mixed numeric types, recursion choosing rep. *)
local
  datatype num = I of IntInf.int | F of real | W of word
  fun eval (I x) = x
    | eval (F r) = IntInf.fromInt (Real.round r)
    | eval (W w) = IntInf.fromInt (Word.toInt w)
  fun build 0 = []
    | build n = (case n mod 4 of
                   0 => I (IntInf.fromInt (n*n))
                 | 1 => F (Real.fromInt n + 0.4)
                 | 2 => W (Word.fromInt n)
                 | _ => I (IntInf.pow (2, n mod 20))) :: build (n-1)
  val total = List.foldl (fn (x,acc) => acc + eval x) 0 (build 40)
in
  val () = print ("@@mixed_datatype=" ^ IntInf.toString total ^ "\n")
end;

(* 8: exception-driven path switch between Int and IntInf on overflow. *)
local
  fun safeMul (a, b) =
      (Int.toLarge (a * b)) handle Overflow => Int.toLarge a * Int.toLarge b
  fun loop (k, acc:IntInf.int) =
      if k > 40 then acc
      else loop (k+1, acc + safeMul (k*1000000, k*1000000))
in
  val () = print ("@@overflow_switch=" ^ IntInf.toString (loop (1,0)) ^ "\n")
end;

(* 9: fold over big list, conditionally applying andb vs add by element size. *)
local
  fun comb (x:IntInf.int, acc:IntInf.int) =
      if x < 256 then IntInf.andb (acc + x, 0xFFFFFFFFFFFF)
      else acc + IntInf.andb (x, 0xFF)
  val xs = List.tabulate (100, fn k => IntInf.fromInt k * IntInf.fromInt k)
  val r = List.foldl comb 1 xs
in
  val () = print ("@@cond_andb_fold=" ^ IntInf.toString r ^ "\n")
end;

(* 10: closure capturing a mutable IntInf ref, crossing boundary. *)
local
  val acc = ref (0 : IntInf.int)
  fun mk thr = (fn x => if x < thr then acc := !acc + IntInf.fromInt x
                        else acc := !acc + IntInf.fromInt x * IntInf.fromInt x)
  val f = mk 50
  val () = List.app f (List.tabulate (100, fn i => i))
in
  val () = print ("@@closure_ref=" ^ IntInf.toString (!acc) ^ "\n")
end;

(* 11: Word arithmetic wrap vs IntInf exact, both computed and compared. *)
local
  fun wsum n = List.foldl (fn (k,acc) => acc + Word.fromInt k) 0w0 (List.tabulate (n, fn i=>i+1))
  fun isum n = List.foldl (fn (k,acc) => acc + IntInf.fromInt k) 0 (List.tabulate (n, fn i=>i+1))
  val w = wsum 1000
  val i = isum 1000
  val s = "W=" ^ Word.toString w ^ ";I=" ^ IntInf.toString i
in
  val () = print ("@@word_vs_intinf=" ^ s ^ "\n")
end;

(* 12: deeply recursive function returning IntInf, with isShort guard
   choosing tail vs non-tail accumulation. andb on intermediate. *)
local
  fun fib (n, a:IntInf.int, b:IntInf.int) =
      if n = 0 then a
      else
        let val nx = a + b
            val masked = if RunCall.isShort nx then nx
                         else IntInf.andb (nx, IntInf.<< (1, 0w200) - 1)
        in fib (n-1, b, masked) end
in
  val () = print ("@@fib_guard=" ^ IntInf.toString (fib (90, 0, 1)) ^ "\n")
end;

(* 13: Real comparison choosing branch, accumulate Int from Real predicate. *)
local
  fun classify r =
      if Real.== (r, Real.realFloor r) then 1     (* integer-valued *)
      else if r > 0.0 then 2 else 3
  val rs = List.tabulate (60, fn k => Real.fromInt k / 4.0)
  val counts = List.foldl (fn (r,(a,b,c)) =>
                  case classify r of 1=>(a+1,b,c) | 2=>(a,b+1,c) | _=>(a,b,c+1))
                  (0,0,0) rs
  val (a,b,c) = counts
in
  val () = print ("@@real_pred=" ^ Int.toString a ^ "," ^ Int.toString b ^ "," ^ Int.toString c ^ "\n")
end;

(* 14: large IntInf bit manipulation in a loop — orb/xorb/andb crossing. *)
local
  fun step (k, acc:IntInf.int) =
      let val bit = IntInf.<< (1, Word.fromInt (k mod 100))
          val acc2 = IntInf.orb (acc, bit)
          val acc3 = IntInf.xorb (acc2, IntInf.<< (acc2, 0w1))
      in IntInf.andb (acc3, IntInf.<< (1, 0w150) - 1) end
  val r = List.foldl step 1 (List.tabulate (120, fn k => k))
in
  val () = print ("@@bitmix_loop=" ^ IntInf.toString r ^ "\n")
end;

(* 15: mutual recursion choosing FixedInt vs IntInf path by magnitude.
   Both arms strictly DIVIDE n down, so it terminates; the isShort guard
   selects an andb/bit path while long vs an arithmetic path once short. *)
local
  fun ping (n:IntInf.int) (acc:IntInf.int) =
      if n <= 1 then acc
      else if RunCall.isShort n
           then pong (n div 2) (acc + (n - 1))                 (* arithmetic, short *)
           else pong (n div 3) (acc + IntInf.andb (n, 0xFFFF)) (* bit path, long *)
  and pong (n:IntInf.int) (acc:IntInf.int) =
      if n <= 1 then acc
      else if RunCall.isShort n
           then ping (n div 2) (acc + IntInf.fromInt 7)
           else ping (n div 2) (acc + IntInf.~>> (IntInf.andb (n, 0xFFFFFF), 0w0))
  val r = ping (IntInf.pow (2, 64) + 12345) 0
in
  val () = print ("@@mutual_rec=" ^ IntInf.toString r ^ "\n")
end;

(* 16: Vector of mixed-rep numbers, map+fold with size-guarded ops. *)
local
  val v = Vector.tabulate (50, fn i =>
            if i mod 2 = 0 then IntInf.fromInt i
            else IntInf.pow (2, i mod 40))
  fun comb (x, acc) =
      if RunCall.isShort x andalso RunCall.isShort acc
      then acc + x
      else acc + IntInf.andb (x, 0xFFFFFF) + IntInf.~>> (x, 0w8)
  val r = Vector.foldl comb 0 v
in
  val () = print ("@@vec_mix=" ^ IntInf.toString r ^ "\n")
end;
