(* fuzz_real32_rts.sml — DETERMINISTIC differential fuzz driver (domain: Real32 / RTS).
 * ===========================================================================
 * Sweep seat REAL32: the PolyRealF* RTS family — Real32 transcendentals
 * (PolyRealFSqrt/FSin/FCos/FTan/FArcSin/FArcCos/FArctan/FSinh/FCosh/FTanh/
 *  FExp/FLog/FLog10), the rounding family (FFloor/FCeil/FRound/FTrunc), and the
 * binary RTS ops (FAtan2/FCopySign/FNextAfter/FPow/FRem) — plus the
 * Real32<->Real / Real32<->Int conversion paths (fromInt/fromLarge/toLarge/
 * fromLargeInt/floor/ceil/round/trunc).
 *
 * Unlike the +,-,*,/ and comparison ops (which are plain float bytecode
 * opcodes, NOT RTS), the Math.* / rem / copySign / nextAfter / pow / atan2 /
 * floor-family functions ARE the rtsCallFastF_F / rtsCallFastFF_F calls
 * (basis/Real.sml:768-787, 672-697) — i.e. they dispatch straight into the
 * PolyRealF* RTS emulation (rts.rs:438-556) with NO inline twin. So for these
 * the "_rts_" form IS the only form; we still emit "_inline_" (a syntactically
 * direct call) and "_rts_" (ref-forced through `I32`) so the harness shape
 * matches the rest of the corpus and any opcode-vs-RTS difference would show.
 *
 * SEED + LCG: identical Knuth/PCG recurrence (state0 = 0w1, mult
 * 0x5851F42D4C957F2D, inc 0x14057B7EF767814F) used by fuzz_word.sml — the
 * Word64 stream is bit-identical across our `poly run` and both upstream
 * oracles, so both sides consume the SAME random operands.
 *
 * OPERAND CLASSES (randReal32): normal across a wide exponent band, subnormal,
 * +0.0, ~0.0, +inf, ~inf, nan — to stress the IEEE corner handling in the RTS.
 *
 * DETERMINISM / OUTPUT STABILITY: results are stringified by Real32.fmt SCI(7)
 * (verified byte-stable on same-arch across all three engines) with specials
 * mapped to fixed tokens via `cls` (NAN / PINF / NINF / ~0.0); booleans by
 * Bool.toString; conversions that can raise wrapped to OVF/DOM/EXN. NO bare
 * Real32.toString of a value that could carry ULP noise.
 *
 * KNOWN-DIVERGENCE ALLOW-LIST (NOT our bug — see report): upstream's
 * RealArithmetic::Init (libpolyml/reals.cpp:918-919) sets `notANumber = NAN`
 * inside `#if (defined(NAN))` but FORGETS to set `notANumberF`, so the f32
 * not-a-number global is left zero-initialized to 0.0. Consequently upstream's
 * PolyRealFLog/FLog10/FArcSin/FArcCos return FINITE 0.0 (not NaN) for
 * out-of-domain inputs (ln/log10 of a NEGATIVE; asin/acos outside [-1,1]).
 * Ours returns the IEEE-correct NaN. To keep this driver a GREEN regression
 * fence we DO NOT feed out-of-domain values to those four functions here; the
 * divergence is documented + reproduced separately in the seat report and is
 * flagged for human (it is a latent UPSTREAM bug, like the andb/orb stage-0
 * case — we are MORE correct, but it is not auto-fixable to "match" without
 * deliberately reproducing an uninitialized-global bug). ln/log10 at exactly
 * 0.0 (-> -inf) and the in-domain ranges ARE exercised and DO agree.
 *)

(* ---- ref-force: defeats inline specialization, routes through the RTS ---- *)
fun I32 (x : Real32.real) = let val r = ref x in !r end;
fun I   (x : real)        = let val r = ref x in !r end;
fun II  (x : int)         = let val r = ref x in !r end;

(* ---- 64-bit LCG (Knuth/PCG constants, seed 0w1) ---- *)
val st = ref (0w1 : Word64.word);
fun step () = (st := !st * 0wx5851F42D4C957F2D + 0wx14057B7EF767814F; !st);
fun rbits () = Word64.toInt (Word64.>> (step (), 0w33));   (* 0 .. 2^31-1 *)
fun rrange n = (rbits ()) mod n;
fun rsign () = if rrange 2 = 0 then 1 else ~1;

(* ---- printing + stable stringifiers ---- *)
fun p s = print (s ^ "\n");
val bs = Bool.toString;

(* classify a Real32 into a byte-stable token; finite values rendered SCI(7) *)
fun cls x =
  if Real32.isNan x then "NAN"
  else if Real32.isFinite x then
    (if Real32.== (x, 0.0) andalso Real32.signBit x then "~0.0"
     else Real32.fmt (StringCvt.SCI (SOME 7)) x)
  else if Real32.signBit x then "NINF" else "PINF";

(* classify a Real (double) the same way *)
fun clsD x =
  if Real.isNan x then "NAN"
  else if Real.isFinite x then
    (if Real.== (x, 0.0) andalso Real.signBit x then "~0.0"
     else Real.fmt (StringCvt.SCI (SOME 7)) x)
  else if Real.signBit x then "NINF" else "PINF";

(* ---- specials ---- *)
val inf32  = Real32.fromInt 1 / Real32.fromInt 0;
val ninf32 = ~(Real32.fromInt 1) / Real32.fromInt 0;
val nan32  = Real32.fromInt 0 / Real32.fromInt 0;
val nz32   = ~0.0 : Real32.real;

(* a random Real32 across magnitude classes / specials *)
fun randReal32 () =
  let val tag = rrange 18 in
    if tag = 0 then 0.0 else
    if tag = 1 then nz32 else
    if tag = 2 then inf32 else
    if tag = 3 then ninf32 else
    if tag = 4 then nan32 else
    if tag = 5 then
      (* a subnormal: smallest-subnormal scaled by a small int *)
      Real32.fromInt (rsign ()) * (Real32.nextAfter (0.0, 1.0)) * Real32.fromInt (1 + rrange 100)
    else
      let
        val man = Real32.fromInt (1 + rrange 16000000)
        val e   = (rrange 70) - 35           (* ~2^-35 .. 2^35 *)
        val s   = Real32.fromInt (rsign ())
      in s * Real32.fromManExp { man = man, exp = e } end
  end;

(* a random Real32 biased toward the trig-sensible range [-pi*4, pi*4] plus
   the occasional special, for sin/cos/tan/atan/sinh/cosh/tanh/exp. *)
fun randAngle32 () =
  let val tag = rrange 12 in
    if tag = 0 then 0.0 else
    if tag = 1 then nz32 else
    if tag = 2 then inf32 else
    if tag = 3 then ninf32 else
    if tag = 4 then nan32 else
      let val s = Real32.fromInt (rsign ())
          val whole = Real32.fromInt (rrange 13)       (* 0..12 *)
          val frac  = Real32.fromInt (rrange 1000) / 1000.0
      in s * (whole + frac) end
  end;

(* a NON-NEGATIVE, NON-NaN Real32 for ln / log10 (STRICTLY in-domain — see the
   allow-list note: out-of-domain ln/log10, which here means NEGATIVE *or* NaN,
   hit the upstream notANumberF=0.0 bug). Includes exactly 0.0 (ln 0 -> -inf,
   agrees) and +inf (ln inf -> inf, agrees). Deliberately NO nan32. *)
fun randPos32 () =
  let val tag = rrange 10 in
    if tag = 0 then 0.0 else
    if tag = 1 then inf32 else
      let val man = Real32.fromInt (1 + rrange 16000000)
          val e   = (rrange 60) - 30
      in Real32.fromManExp { man = man, exp = e } end   (* always >= 0, never NaN *)
  end;

(* a Real32 STRICTLY in [-1.0, 1.0] for asin/acos plus the boundaries +/-1.
   Out-of-[-1,1] AND NaN both hit the notANumberF bug, so NO nan32 here. *)
fun randUnit32 () =
  let val tag = rrange 9 in
    if tag = 0 then 1.0 else
    if tag = 1 then ~1.0 else
    if tag = 2 then 0.0 else
      Real32.fromInt (rsign ()) * (Real32.fromInt (rrange 1001) / 1000.0)
  end;

(* a Real32 angle generator that EXCLUDES NaN (for pow, whose nan-base path
   returns the buggy notANumberF=0.0 upstream). Keeps +/-inf and +/-0. *)
fun randAngleNoNan32 () =
  let val tag = rrange 11 in
    if tag = 0 then 0.0 else
    if tag = 1 then nz32 else
    if tag = 2 then inf32 else
    if tag = 3 then ninf32 else
      let val s = Real32.fromInt (rsign ())
          val whole = Real32.fromInt (rrange 13)
          val frac  = Real32.fromInt (rrange 1000) / 1000.0
      in s * (whole + frac) end
  end;

(* a random int across magnitude classes for fromInt. *)
fun randInt () =
  (case rrange 5 of
       0 => (rrange 201) - 100
     | 1 => rsign () * (rrange 1000000000)
     | 2 => rsign () * (4611686018427387900 - rrange 8)   (* near 2^62 *)
     | 3 => rsign () * (rrange 1000)
     | _ => rsign () * (1000000000000 + rrange 1000000000));

(* a random double for fromLarge / toLarge-roundtrip. *)
fun randReal () =
  let val tag = rrange 14 in
    if tag = 0 then 0.0 else
    if tag = 1 then ~0.0 else
    if tag = 2 then 1.0 / 0.0 else
    if tag = 3 then ~1.0 / 0.0 else
    if tag = 4 then 0.0 / 0.0 else
      let val man = Real.fromInt (1 + rrange 2000000000)
          val e   = (rrange 80) - 40
          val s   = Real.fromInt (rsign ())
      in s * Real.fromManExp { man = man, exp = e } end
  end;

(* ===================================================================== *)
(* EMITTERS — each emits _inline_ (direct) + _rts_ (ref-forced).          *)
(* For Real32 transcendentals BOTH dispatch to the same PolyRealF* RTS    *)
(* call; the two labels still let an opcode-vs-RTS difference show.        *)
(* ===================================================================== *)

(* Real32 unary, result Real32 -> cls *)
fun emitU1 (nm, f, gen, n) =
  let fun go i = if i >= n then () else
        let val a = gen ()
        in p ("@@" ^ nm ^ "_inline_" ^ Int.toString i ^ "=" ^ cls (f a));
           p ("@@" ^ nm ^ "_rts_"    ^ Int.toString i ^ "=" ^ cls (f (I32 a)));
           go (i + 1)
        end
  in go 0 end;

(* Real32 binary, result Real32 -> cls *)
fun emitB2 (nm, f, gen, n) =
  let fun go i = if i >= n then () else
        let val a = gen () and b = gen ()
        in p ("@@" ^ nm ^ "_inline_" ^ Int.toString i ^ "=" ^ cls (f (a, b)));
           p ("@@" ^ nm ^ "_rts_"    ^ Int.toString i ^ "=" ^ cls (f (I32 a, I32 b)));
           go (i + 1)
        end
  in go 0 end;

(* Real32 unary that may raise (floor/ceil/round/trunc) -> Int, wrapped *)
fun emitConv (nm, f, gen, n) =
  let fun safe x = (Int.toString (f x)) handle Overflow=>"OVF" | General.Domain=>"DOM" | Div=>"DIV" | _=>"EXN"
      fun go i = if i >= n then () else
        let val a = gen ()
        in p ("@@" ^ nm ^ "_inline_" ^ Int.toString i ^ "=" ^ safe a);
           p ("@@" ^ nm ^ "_rts_"    ^ Int.toString i ^ "=" ^ safe (I32 a));
           go (i + 1)
        end
  in go 0 end;

(* ===================================================================== *)
(* RUN                                                                    *)
(* ===================================================================== *)

(* --- transcendentals defined on the whole line (specials exercised) --- *)
val () = emitU1 ("r32sin",  Real32.Math.sin,  randAngle32, 12);
val () = emitU1 ("r32cos",  Real32.Math.cos,  randAngle32, 12);
val () = emitU1 ("r32tan",  Real32.Math.tan,  randAngle32, 12);
val () = emitU1 ("r32atan", Real32.Math.atan, randReal32,  12);
val () = emitU1 ("r32exp",  Real32.Math.exp,  randAngle32, 12);
val () = emitU1 ("r32sinh", Real32.Math.sinh, randAngle32, 12);
val () = emitU1 ("r32cosh", Real32.Math.cosh, randAngle32, 12);
val () = emitU1 ("r32tanh", Real32.Math.tanh, randAngle32, 12);

(* --- sqrt: defined on [0,inf]; sqrt of negative IS NaN on BOTH (no guard) --- *)
val () = emitU1 ("r32sqrt", Real32.Math.sqrt, randReal32, 12);

(* --- ln / log10: in-domain only (non-negative); 0.0 -> -inf agrees.
       Out-of-domain (negative) hits the upstream notANumberF bug -> NOT here. --- *)
val () = emitU1 ("r32ln",    Real32.Math.ln,    randPos32, 12);
val () = emitU1 ("r32log10", Real32.Math.log10, randPos32, 12);

(* --- asin / acos: in-domain only ([-1,1]); out-of-range hits notANumberF. --- *)
val () = emitU1 ("r32asin", Real32.Math.asin, randUnit32, 12);
val () = emitU1 ("r32acos", Real32.Math.acos, randUnit32, 12);

(* --- binary RTS: atan2 / pow / rem / copySign / nextAfter --- *)
val () = emitB2 ("r32atan2",    Real32.Math.atan2,                          randReal32, 12);
(* pow: NaN BASE returns the buggy notANumberF=0.0 upstream, so the base
   generator excludes NaN. A NaN exponent (with a finite base) returns nan on
   both (agrees), so the exponent generator may include NaN — but to keep both
   operands from the same NaN-free stream we use randAngleNoNan32 for both. *)
val () = emitB2 ("r32pow",      Real32.Math.pow,                            randAngleNoNan32, 14);
val () = emitB2 ("r32rem",      Real32.rem,                                 randReal32, 12);
val () = emitB2 ("r32copysign", Real32.copySign,                            randReal32, 12);
val () = emitB2 ("r32nextafter",Real32.nextAfter,                           randReal32, 12);

(* --- rounding family: realFloor/realCeil/realRound/realTrunc (Real32 -> Real32) --- *)
val () = emitU1 ("r32realfloor", Real32.realFloor, randReal32, 10);
val () = emitU1 ("r32realceil",  Real32.realCeil,  randReal32, 10);
val () = emitU1 ("r32realround", Real32.realRound, randReal32, 10);
val () = emitU1 ("r32realtrunc", Real32.realTrunc, randReal32, 10);

(* --- to-Int rounding family (may raise OVF on inf / DOM on nan) --- *)
val () = emitConv ("r32floor", Real32.floor, randReal32, 12);
val () = emitConv ("r32ceil",  Real32.ceil,  randReal32, 12);
val () = emitConv ("r32round", Real32.round, randReal32, 12);
val () = emitConv ("r32trunc", Real32.trunc, randReal32, 12);

(* --- conversions: fromInt (inline + ref-forced) --- *)
local
  fun go i = if i >= 16 then () else
    let val x = randInt ()
    in p ("@@r32fromint_inline_" ^ Int.toString i ^ "=" ^ cls (Real32.fromInt x));
       p ("@@r32fromint_rts_"    ^ Int.toString i ^ "=" ^ cls (Real32.fromInt (II x)));
       go (i + 1)
    end
in val () = go 0 end;

(* --- conversions: fromLarge (Real -> Real32, TO_NEAREST) --- *)
local
  fun go i = if i >= 16 then () else
    let val x = randReal ()
    in p ("@@r32fromlarge_inline_" ^ Int.toString i ^ "=" ^ cls (Real32.fromLarge IEEEReal.TO_NEAREST x));
       p ("@@r32fromlarge_rts_"    ^ Int.toString i ^ "=" ^ cls (Real32.fromLarge IEEEReal.TO_NEAREST (I x)));
       go (i + 1)
    end
in val () = go 0 end;

(* --- conversions: toLarge (Real32 -> Real) --- *)
local
  fun go i = if i >= 16 then () else
    let val x = randReal32 ()
    in p ("@@r32tolarge_inline_" ^ Int.toString i ^ "=" ^ clsD (Real32.toLarge x));
       p ("@@r32tolarge_rts_"    ^ Int.toString i ^ "=" ^ clsD (Real32.toLarge (I32 x)));
       go (i + 1)
    end
in val () = go 0 end;

(* --- conversions: fromLargeInt (IntInf -> Real32) --- *)
local
  fun bigOf () : IntInf.int =
    let val sgn : IntInf.int = if rrange 2 = 0 then 1 else ~1
        val cls = rrange 3
    in sgn * (case cls of
                0 => IntInf.fromInt (rrange 201 - 100)
              | 1 => IntInf.pow (2, 62) + IntInf.fromInt (rrange 2001 - 1000)
              | _ => IntInf.pow (2, 40 + rrange 80) + IntInf.fromInt (rrange 1000000))
    end
  fun I_big (x : IntInf.int) = let val r = ref x in !r end
  fun go i = if i >= 16 then () else
    let val x = bigOf ()
    in p ("@@r32fromlargeint_inline_" ^ Int.toString i ^ "=" ^ cls (Real32.fromLargeInt x));
       p ("@@r32fromlargeint_rts_"    ^ Int.toString i ^ "=" ^ cls (Real32.fromLargeInt (I_big x)));
       go (i + 1)
    end
in val () = go 0 end;

(* --- a small DELIBERATE in-domain edge sweep (deterministic, not random) --- *)
val () = p ("@@edge_ln0=" ^ cls (Real32.Math.ln (I32 0.0)));            (* -inf, agrees *)
val () = p ("@@edge_ln_neg0=" ^ cls (Real32.Math.ln (I32 nz32)));      (* -inf, agrees *)
val () = p ("@@edge_log10_0=" ^ cls (Real32.Math.log10 (I32 0.0)));    (* -inf, agrees *)
val () = p ("@@edge_asin_1=" ^ cls (Real32.Math.asin (I32 1.0)));
val () = p ("@@edge_acos_neg1=" ^ cls (Real32.Math.acos (I32 (~1.0))));
val () = p ("@@edge_pow_negzero_3=" ^ cls (Real32.Math.pow (I32 nz32, I32 3.0)));
val () = p ("@@edge_pow_0_0=" ^ cls (Real32.Math.pow (I32 0.0, I32 0.0)));
val () = p ("@@edge_copysign_nan_neg_signbit=" ^ bs (Real32.signBit (Real32.copySign (I32 nan32, I32 (~1.0)))));
val () = p ("@@edge_nextafter_nan=" ^ cls (Real32.nextAfter (I32 nan32, I32 1.0)));
val () = p ("@@edge_rem_5_0=" ^ cls (Real32.rem (I32 5.0, I32 0.0)));

val () = p "@@FUZZ_REAL32_RTS_DONE=1";
