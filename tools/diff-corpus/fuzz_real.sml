(* diff-corpus category: fuzz_real — DETERMINISTIC DIFFERENTIAL FUZZ DRIVER
   ===========================================================================
   This is a FUZZ DRIVER, not a hand-picked corpus. It builds a deterministic
   stream of operands with a hand-rolled 64-bit LCG PRNG and applies the whole
   Real / Real32 operator domain to each, emitting one @@<label>=<value> line
   per case. Because the PRNG is pure SML and 64-bit-word arithmetic is
   well-defined identically on upstream PolyML and on our Rust interpreter, both
   sides consume the SAME random sequence and must agree value-for-value. Any
   @@ line that differs is a faithfulness bug in OUR port.

   SEED: LCG state starts at 0w1 (Word64), recurrence
     s := s * 0x5851F42D4C957F2D + 0x14057B7EF767814F  (Knuth/PCG multiplier)
   so the whole run is reproducible. Change nothing here without rebuilding the
   expected diff baseline.

   DOMAIN (this driver): real
     Real  : + - * /, ~, abs, < <= = ?= (unordered-eq) != (Real.!=),
             Real.rem, round/floor/ceil/trunc/realRound, Real.toLargeInt
             (TO_NEAREST), Real.fromInt
     Real32: + - * /, ~, abs, < <= = ?=, plus a few conversions
     special values: 0.0, ~0.0, posInf (1.0/0.0), negInf (~1.0/0.0),
                     nan (0.0/0.0) are seeded into the operand pool.

   INLINE vs REF-FORCED: every binary/unary op is emitted twice —
     - INLINE form     `a OP b`        (hits the bytecode opcode path)
     - REF-FORCED form  `I a OP I b`   where `fun I x = let val r=ref x in !r end`
       defeats inline specialization so the op dispatches through the boxed
       runtime emulation path (the analogue of the Poly*Arbitrary RTS class that
       hid the subtraction-negation bug).
   Labels: @@<op>_inline_<i> and @@<op>_rts_<i>.

   DETERMINISM RULES: outputs are Real.toString / Real32.toString /
   Bool.toString / IntInf.toString / Int.toString only — all PolyML's own,
   platform-stable on same-arch. Operations that can raise (conversions on
   nan/inf/out-of-range) are wrapped so the exception becomes a comparable
   STRING value ("OVF"/"DOM"/"EXN") — both sides raising the same class agree,
   not diverge. Real.toString of nan/inf/~inf/~0.0 is stable ("nan"/"inf"/
   "~inf"/"~0.0") — verified against both builds before writing this driver. *)

(* ---- ref-force helper: defeats inline specialization ---- *)
fun I (x : real)        = let val r = ref x in !r end;
fun I32 (x : Real32.real) = let val r = ref x in !r end;
fun II (x : int)        = let val r = ref x in !r end;

(* ---- 64-bit LCG ---- *)
val lcg = ref (0w1 : Word64.word);
fun step () = (lcg := !lcg * 0w6364136223846793005 + 0w1442695040888963407; !lcg);
(* a 31-bit non-negative int from the high bits (avoid low-bit LCG weakness) *)
fun rbits () = Word64.toInt (Word64.>> (step (), 0w33));   (* 0 .. 2^31-1 *)
fun rrange n = (rbits ()) mod n;                            (* 0 .. n-1 *)
fun rsign () = if rrange 2 = 0 then 1 else ~1;

(* ---- operand generators across magnitude classes ----------------------- *)

(* a random REAL across magnitude classes, occasionally a special value. *)
fun randReal () =
  let val tag = rrange 16 in
    if tag = 0 then 0.0
    else if tag = 1 then ~0.0
    else if tag = 2 then 1.0 / 0.0          (* +inf *)
    else if tag = 3 then ~1.0 / 0.0         (* -inf *)
    else if tag = 4 then 0.0 / 0.0          (* nan  *)
    else
      let
        (* mantissa 1 .. ~2^31, exponent across a wide range incl. denormal
           and overflow neighbourhoods *)
        val man = Real.fromInt (1 + rrange 2000000000)
        val e   = (rrange 240) - 120        (* ~ 2^-120 .. 2^120 *)
        val s   = Real.fromInt (rsign ())
      in s * Real.fromManExp { man = man, exp = e } end
  end;

(* a random REAL biased toward the int-conversion-interesting range
   (small / near-integer / near tagged-int boundary 2^62). *)
fun randConvReal () =
  let val tag = rrange 12 in
    if tag = 0 then 0.0 / 0.0               (* nan -> conv raises *)
    else if tag = 1 then 1.0 / 0.0          (* inf -> conv raises/overflow *)
    else if tag = 2 then ~1.0 / 0.0
    else
      let
        val whole = Real.fromInt ((rrange 4000000) - 2000000)
        (* a fractional part in {.0 .25 .5 .75 .x} to exercise rounding ties *)
        val frac  = (case rrange 5 of 0 => 0.0 | 1 => 0.25 | 2 => 0.5
                                    | 3 => 0.75 | _ => Real.fromInt (rrange 1000) / 1000.0)
        val s     = Real.fromInt (rsign ())
        (* occasionally scale toward the tagged-int boundary 2^62 *)
        val scaled = if rrange 4 = 0
                     then (whole + frac) * 4.6e18   (* ~ near/over 2^62 *)
                     else whole + frac
      in s * scaled end
  end;

(* a random Real32 across magnitude classes / specials. *)
fun randReal32 () =
  let val tag = rrange 16 in
    if tag = 0 then 0.0 else
    if tag = 1 then ~0.0 else
    if tag = 2 then Real32.fromInt 1 / Real32.fromInt 0 else      (* +inf *)
    if tag = 3 then ~(Real32.fromInt 1) / Real32.fromInt 0 else   (* -inf *)
    if tag = 4 then Real32.fromInt 0 / Real32.fromInt 0 else      (* nan  *)
      let
        val man = Real32.fromInt (1 + rrange 16000000)
        val e   = (rrange 60) - 30
        val s   = Real32.fromInt (rsign ())
      in s * Real32.fromManExp { man = man, exp = e } end
  end;

(* random int across magnitude classes for Real.fromInt. *)
fun randInt () =
  (case rrange 5 of
       0 => (rrange 201) - 100                              (* small -100..100 *)
     | 1 => rsign () * (rrange 1000000000)                  (* mid *)
     | 2 => rsign () * (4611686018427387900 - rrange 8)     (* near 2^62 tagged boundary *)
     | 3 => rsign () * (rrange 1000)                        (* tiny *)
     | _ => rsign () * (1000000000000 + rrange 1000000000));(* large but in FixedInt *)

(* ---- emitters ---------------------------------------------------------- *)
fun p (s : string) = print (s ^ "\n");
val rs = Real.toString;
val r32s = Real32.toString;

(* Real binary op: inline + ref-forced, result stringified by `show`. *)
fun emitRR (op_name, f, show, n) =
  let
    fun go i =
      if i >= n then () else
      let
        val a = randReal () and b = randReal ()
        (* INLINE: pass through directly (opcode path) *)
        val () = p ("@@" ^ op_name ^ "_inline_" ^ Int.toString i ^ "=" ^ show (f (a, b)))
        (* REF-FORCED: launder through ref to defeat inline specialization *)
        val () = p ("@@" ^ op_name ^ "_rts_"    ^ Int.toString i ^ "=" ^ show (f (I a, I b)))
      in go (i + 1) end
  in go 0 end;

(* Real unary op. *)
fun emitR1 (op_name, f, show, n) =
  let
    fun go i =
      if i >= n then () else
      let
        val a = randReal ()
        val () = p ("@@" ^ op_name ^ "_inline_" ^ Int.toString i ^ "=" ^ show (f a))
        val () = p ("@@" ^ op_name ^ "_rts_"    ^ Int.toString i ^ "=" ^ show (f (I a)))
      in go (i + 1) end
  in go 0 end;

(* Real conversion that may raise: wrap into a comparable string value. *)
fun emitConv (op_name, f, n) =
  let
    fun safe x = (f x) handle Overflow => "OVF"
                            | General.Domain => "DOM"
                            | Div => "DIV"
                            | _ => "EXN"
    fun go i =
      if i >= n then () else
      let
        val a = randConvReal ()
        val () = p ("@@" ^ op_name ^ "_inline_" ^ Int.toString i ^ "=" ^ safe a)
        val () = p ("@@" ^ op_name ^ "_rts_"    ^ Int.toString i ^ "=" ^ safe (I a))
      in go (i + 1) end
  in go 0 end;

(* Real32 binary op. *)
fun emit32 (op_name, f, show, n) =
  let
    fun go i =
      if i >= n then () else
      let
        val a = randReal32 () and b = randReal32 ()
        val () = p ("@@" ^ op_name ^ "_inline_" ^ Int.toString i ^ "=" ^ show (f (a, b)))
        val () = p ("@@" ^ op_name ^ "_rts_"    ^ Int.toString i ^ "=" ^ show (f (I32 a, I32 b)))
      in go (i + 1) end
  in go 0 end;

(* Real32 unary op. *)
fun emit321 (op_name, f, show, n) =
  let
    fun go i =
      if i >= n then () else
      let
        val a = randReal32 ()
        val () = p ("@@" ^ op_name ^ "_inline_" ^ Int.toString i ^ "=" ^ show (f a))
        val () = p ("@@" ^ op_name ^ "_rts_"    ^ Int.toString i ^ "=" ^ show (f (I32 a)))
      in go (i + 1) end
  in go 0 end;

(* fromInt: deterministic int -> real, inline + ref-forced. *)
fun emitFromInt n =
  let
    fun go i =
      if i >= n then () else
      let
        val x = randInt ()
        val () = p ("@@fromint_inline_" ^ Int.toString i ^ "=" ^ rs (Real.fromInt x))
        val () = p ("@@fromint_rts_"    ^ Int.toString i ^ "=" ^ rs (Real.fromInt (II x)))
        val () = p ("@@fromint32_inline_" ^ Int.toString i ^ "=" ^ r32s (Real32.fromInt x))
        val () = p ("@@fromint32_rts_"    ^ Int.toString i ^ "=" ^ r32s (Real32.fromInt (II x)))
      in go (i + 1) end
  in go 0 end;

val bs = Bool.toString;

(* ===================================================================== *)
(* RUN. Counts chosen so the total @@ line count lands in the 150-300+    *)
(* "many cases" band requested. Each emit* call produces 2*n @@ lines     *)
(* (inline + rts).                                                        *)
(* ===================================================================== *)

(* --- Real arithmetic: + - * / rem --- *)
val () = emitRR ("add", Real.+, rs, 14);
val () = emitRR ("sub", Real.-, rs, 14);
val () = emitRR ("mul", Real.*, rs, 14);
val () = emitRR ("dvd", Real./, rs, 14);
val () = emitRR ("rem", Real.rem, rs, 14);

(* --- Real unary: ~ abs --- *)
val () = emitR1 ("neg", Real.~, rs, 10);
val () = emitR1 ("abs", Real.abs, rs, 10);

(* --- Real comparisons: < <= = ?= != --- *)
val () = emitRR ("lt",  fn (a,b) => Real.< (a,b),  bs, 10);
val () = emitRR ("le",  fn (a,b) => Real.<= (a,b), bs, 10);
val () = emitRR ("eq",  fn (a,b) => Real.== (a,b), bs, 10);
val () = emitRR ("uneq", fn (a,b) => Real.?= (a,b), bs, 10);  (* unordered-or-equal *)
val () = emitRR ("neq", fn (a,b) => Real.!= (a,b), bs, 10);

(* --- Real conversions (may raise -> string) --- *)
val () = emitConv ("round",     fn x => Int.toString (Real.round x), 12);
val () = emitConv ("floor",     fn x => Int.toString (Real.floor x), 12);
val () = emitConv ("ceil",      fn x => Int.toString (Real.ceil x), 12);
val () = emitConv ("trunc",     fn x => Int.toString (Real.trunc x), 12);
val () = emitConv ("realround", fn x => rs (Real.realRound x), 12);
val () = emitConv ("tolargeint",
                   fn x => IntInf.toString (Real.toLargeInt IEEEReal.TO_NEAREST x), 12);

(* --- Real.fromInt across magnitude classes --- *)
val () = emitFromInt 14;

(* --- Real32 arithmetic + - * / --- *)
val () = emit32 ("r32add", Real32.+, r32s, 10);
val () = emit32 ("r32sub", Real32.-, r32s, 10);
val () = emit32 ("r32mul", Real32.*, r32s, 10);
val () = emit32 ("r32dvd", Real32./, r32s, 10);

(* --- Real32 unary ~ abs --- *)
val () = emit321 ("r32neg", Real32.~, r32s, 8);
val () = emit321 ("r32abs", Real32.abs, r32s, 8);

(* --- Real32 comparisons < <= = ?= --- *)
val () = emit32 ("r32lt", fn (a,b) => Real32.< (a,b),  bs, 8);
val () = emit32 ("r32le", fn (a,b) => Real32.<= (a,b), bs, 8);
val () = emit32 ("r32eq", fn (a,b) => Real32.== (a,b), bs, 8);
val () = emit32 ("r32uneq", fn (a,b) => Real32.?= (a,b), bs, 8);

(* a final sentinel so a truncated run is detectable *)
val () = p ("@@DONE=ok");
