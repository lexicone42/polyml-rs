(* diff-corpus: fuzz_convert.sml — DETERMINISTIC differential FUZZ DRIVER (2026-06-17)
   ==============================================================================
   Domain: CROSS-TYPE CONVERSIONS across magnitude/sign classes.  This is a *fuzz*
   driver: a hand-rolled 64-bit-style LCG PRNG (seeded below) drives operand
   generation so the byte stream of random numbers is IDENTICAL on upstream PolyML
   and on our `poly run` — both interpreters consume the SAME random sequence and
   must therefore produce identical @@values.  Any divergence is a faithfulness bug
   in OUR port.

   PRNG: the classic Knuth/PCG LCG constants on a Word.word.  This FixedInt basis
   has Word.wordSize = 63, so Word multiply/add is mod 2^63 — still a perfectly
   deterministic full-period-ish generator, bit-identical on both sides.
       s := s*6364136223846793005 + 1442695040888963407   (mod 2^63)
   We take the high bits (>> 11) as the raw draw, then map into magnitude classes.

   SEED: 0w1 (fixed).  Re-running gives the byte-identical corpus every time.

   For each generated value v and each conversion we emit TWO cases:
     @@<conv>_inline_<i>  :  CONV v          — bytecode opcode path (inline spec.)
     @@<conv>_rts_<i>     :  CONV (I v)      — ref-forced; defeats inline
                                               specialization so the conversion
                                               dispatches through the RTS
                                               Poly*ToLong / PolySignedToLong /
                                               arbitrary-precision emulation path.
                                               THIS is the path where the
                                               PolySubtractArbitrary negation bug
                                               lived (Tests/Test101, fixed dcdbbd4)
                                               — see
                                               docs/upstream-testsuite-findings-2026-06-17.md.

   COVERAGE (cross-type conversions, each exercising its own RTS path):
     - Int.toLarge / Int.fromLarge       (Int <-> LargeInt; default int IS 63-bit
                                          FixedInt, LargeInt IS IntInf in this basis)
     - IntInf.toInt / IntInf.fromInt     (+ Overflow when out of FixedInt range)
     - Word.fromInt / toInt / toIntX / fromLargeInt / toLargeInt / toLargeIntX
     - Word.fromLargeWord / toLargeWord / toLargeWordX  (Word <-> LargeWord)
     - Word8 / Word32: fromLargeInt, toInt, toIntX, fromLarge, toLarge, toLargeX
       (LargeWord <-> Word8 / Word32 width-changing conversions)
     - Int <-> Word round-trips
     - Real.fromLargeInt / Real.toLargeInt (with each IEEEReal rounding mode)

   Anything that can raise (Overflow on the narrowing/sign-sensitive paths,
   Domain on Real.toLargeInt of NaN, Overflow on Real.toLargeInt of Inf) is caught
   and stringified to a comparable VALUE so that "both sides raise" is an
   AGREEMENT, not a divergence.

   Outputs are fully deterministic + platform-stable: IntInf/LargeInt/Int/Word*
   .toString and Real.toString (verified byte-identical on both same-arch builds
   for the value families generated here — no time, no addresses).  Run:
       tools/diff-oracle.sh tools/diff-corpus/fuzz_convert.sml
*)

(* ------------------------------------------------------------------ PRNG --- *)
val s = ref (0w1 : Word.word)
fun nxtW () =
  ( s := !s * 0w6364136223846793005 + 0w1442695040888963407
  ; Word.>> (!s, 0w11) )                          (* a ~52-bit non-negative Word *)
fun nxt () : IntInf.int = Word.toLargeInt (nxtW ())

(* ref-force: a value read back out of a ref cannot be inline-specialized by the
   compiler, so the conversion dispatches through the RTS path. *)
fun I x = let val r = ref x in !r end

(* a draw reduced into 0..(m-1) (m a small positive Int) *)
fun rangeInt (m : int) : int = Word.toInt (Word.mod (nxtW (), Word.fromInt m))

(* a random sign: 1 or ~1 as IntInf *)
fun rndSign () : IntInf.int = if rangeInt 2 = 0 then 1 else ~1

(* ------------------------------------------------------ operand generation --- *)
(* A LargeInt (= IntInf) operand across magnitude classes, with a random sign.
   class 0: small         -100 .. 100
   class 1: near tagged boundary   ~2^62 +/- small        (FixedInt tag edge)
   class 2: big boxed bignum       2^80 .. 2^300, random sign
   We deliberately straddle the FixedInt range (|x| < 2^62) so the IntInf->Int
   and Real->LargeInt narrowing paths see both in-range and overflow operands. *)
val twoPow62 = IntInf.pow (2, 62)

fun genClassII (c : int) : IntInf.int =
  case c of
    0 => (rndSign ()) * (nxt () mod 101)                       (* -100..100 *)
  | 1 => let val delta = (nxt () mod 201) - 100                (* -100..100 *)
         in (rndSign ()) * (twoPow62 + delta) end
  | _ => let val e = 80 + (IntInf.toInt (nxt () mod 221))      (* exp 80..300 *)
             val mag = IntInf.pow (2, e) + (nxt () mod (IntInf.pow (2, 40)))
         in (rndSign ()) * mag end

fun classOf () : int = IntInf.toInt (nxt () mod 3)             (* 0,1,2 *)

(* ------------------------------------------------------------- emit helpers --- *)
fun emit (label, value) = print ("@@" ^ label ^ "=" ^ value ^ "\n")

(* stringify with the raisable conversions caught to comparable sentinels. *)
fun catch (th : unit -> string) : string =
  (th ()) handle Overflow => "OVF"
               | Domain   => "DOM"
               | Div      => "DIV"
               | Size     => "SIZ"
               | _        => "EXN"

(* ------------------------------------------------------------ the fuzz loop --- *)
(* Each iteration draws one operand class, generates one LargeInt operand v, and
   runs every conversion on it in BOTH inline and ref-forced forms.  inline and
   rts forms see the SAME v.  Class is PRNG-chosen so the magnitude/sign mix is
   randomized but deterministic. *)
val nIters = 40

fun istr (i : int) = Int.toString i

fun doIter (i : int) =
  let
    val c   = classOf ()
    val v   = genClassII c                       (* the LargeInt operand        *)
    val si  = istr i
    (* a default-int (63-bit FixedInt) operand in-range, derived from v by
       truncation through Word so Int conversions get an honest 63-bit value too.
       (Width: Word.wordSize = 63 here, so this lands in the FixedInt range.)    *)
    val wAll = Word.fromLargeInt v               (* low 63 bits of |v|-ish       *)
    (* a 64-bit LargeWord operand assembled to exercise the top bit *)
    val lwv  = LargeWord.fromLargeInt v
    fun pair (nm, inlF, rtsF) =
      ( emit (nm ^ "_inline_" ^ si, catch inlF)
      ; emit (nm ^ "_rts_" ^ si,    catch rtsF) )
  in
    (* ---- Int <-> LargeInt -------------------------------------------------- *)
    (* Int.fromLarge narrows IntInf -> 63-bit Int (Overflow if out of range).   *)
    pair ("int_fromLarge",
          fn () => Int.toString (Int.fromLarge v),
          fn () => Int.toString (Int.fromLarge (I v)));
    (* round-trip: take v mod 2^60 into Int range, then Int.toLarge back.        *)
    let val small = IntInf.toInt (v mod (IntInf.pow (2, 60)) - IntInf.pow (2, 59))
    in pair ("int_toLarge",
             fn () => LargeInt.toString (Int.toLarge small),
             fn () => LargeInt.toString (Int.toLarge (I small)));
       pair ("int_largeRT",
             fn () => Int.toString (Int.fromLarge (Int.toLarge small)),
             fn () => Int.toString (Int.fromLarge (Int.toLarge (I small))))
    end;

    (* ---- IntInf.toInt / fromInt -------------------------------------------- *)
    (* IntInf.toInt narrows IntInf -> Int (Overflow out of FixedInt range).      *)
    pair ("intinf_toInt",
          fn () => Int.toString (IntInf.toInt v),
          fn () => Int.toString (IntInf.toInt (I v)));
    (* IntInf.fromInt widens an in-range Int back to IntInf.                     *)
    let val small = IntInf.toInt (v mod 1000000007 - 500000003)
    in pair ("intinf_fromInt",
             fn () => IntInf.toString (IntInf.fromInt small),
             fn () => IntInf.toString (IntInf.fromInt (I small)))
    end;

    (* ---- Word <-> Int ------------------------------------------------------ *)
    (* Word.fromLargeInt truncates to 63 bits (no raise).                        *)
    pair ("word_fromLargeInt",
          fn () => Word.toString (Word.fromLargeInt v),
          fn () => Word.toString (Word.fromLargeInt (I v)));
    (* Word.toInt: Overflow if the top bit is set (>= 2^62 unsigned).            *)
    pair ("word_toInt",
          fn () => Int.toString (Word.toInt wAll),
          fn () => Int.toString (Word.toInt (I wAll)));
    (* Word.toIntX: signed reinterpretation (never raises).                      *)
    pair ("word_toIntX",
          fn () => Int.toString (Word.toIntX wAll),
          fn () => Int.toString (Word.toIntX (I wAll)));
    (* Word.toLargeInt (unsigned -> nonneg IntInf) / toLargeIntX (signed).       *)
    pair ("word_toLargeInt",
          fn () => LargeInt.toString (Word.toLargeInt wAll),
          fn () => LargeInt.toString (Word.toLargeInt (I wAll)));
    pair ("word_toLargeIntX",
          fn () => LargeInt.toString (Word.toLargeIntX wAll),
          fn () => LargeInt.toString (Word.toLargeIntX (I wAll)));
    (* Int <-> Word round-trip: fromInt then toIntX (sign-preserving id).        *)
    let val small = IntInf.toInt (v mod (IntInf.pow (2, 62)) - IntInf.pow (2, 61))
    in pair ("int_word_RT",
             fn () => Int.toString (Word.toIntX (Word.fromInt small)),
             fn () => Int.toString (Word.toIntX (Word.fromInt (I small))))
    end;

    (* ---- Word <-> LargeWord ----------------------------------------------- *)
    (* Word.toLargeWord (zero-extend 63 -> 64) / toLargeWordX (sign-extend).     *)
    pair ("word_toLargeWord",
          fn () => LargeWord.toString (Word.toLargeWord wAll),
          fn () => LargeWord.toString (Word.toLargeWord (I wAll)));
    pair ("word_toLargeWordX",
          fn () => LargeWord.toString (Word.toLargeWordX wAll),
          fn () => LargeWord.toString (Word.toLargeWordX (I wAll)));
    (* Word.fromLargeWord (truncate 64 -> 63).                                   *)
    pair ("word_fromLargeWord",
          fn () => Word.toString (Word.fromLargeWord lwv),
          fn () => Word.toString (Word.fromLargeWord (I lwv)));

    (* ---- LargeWord <-> LargeInt ------------------------------------------- *)
    pair ("largeword_fromLargeInt",
          fn () => LargeWord.toString (LargeWord.fromLargeInt v),
          fn () => LargeWord.toString (LargeWord.fromLargeInt (I v)));
    pair ("largeword_toLargeInt",
          fn () => LargeInt.toString (LargeWord.toLargeInt lwv),
          fn () => LargeInt.toString (LargeWord.toLargeInt (I lwv)));
    pair ("largeword_toLargeIntX",
          fn () => LargeInt.toString (LargeWord.toLargeIntX lwv),
          fn () => LargeInt.toString (LargeWord.toLargeIntX (I lwv)));
    pair ("largeword_toInt",
          fn () => Int.toString (LargeWord.toInt lwv),
          fn () => Int.toString (LargeWord.toInt (I lwv)));
    pair ("largeword_toIntX",
          fn () => Int.toString (LargeWord.toIntX lwv),
          fn () => Int.toString (LargeWord.toIntX (I lwv)));

    (* ---- Word8 (8-bit) conversions ---------------------------------------- *)
    let val w8 = Word8.fromLargeInt v in
      pair ("word8_fromLargeInt",
            fn () => Word8.toString (Word8.fromLargeInt v),
            fn () => Word8.toString (Word8.fromLargeInt (I v)));
      pair ("word8_toInt",
            fn () => Int.toString (Word8.toInt w8),
            fn () => Int.toString (Word8.toInt (I w8)));
      pair ("word8_toIntX",
            fn () => Int.toString (Word8.toIntX w8),
            fn () => Int.toString (Word8.toIntX (I w8)));
      (* Word8 <-> LargeWord width changes *)
      pair ("word8_toLarge",
            fn () => LargeWord.toString (Word8.toLarge w8),
            fn () => LargeWord.toString (Word8.toLarge (I w8)));
      pair ("word8_toLargeX",
            fn () => LargeWord.toString (Word8.toLargeX w8),
            fn () => LargeWord.toString (Word8.toLargeX (I w8)));
      pair ("word8_fromLarge",
            fn () => Word8.toString (Word8.fromLarge lwv),
            fn () => Word8.toString (Word8.fromLarge (I lwv)))
    end;

    (* ---- Word32 (32-bit) conversions -------------------------------------- *)
    let val w32 = Word32.fromLargeInt v in
      pair ("word32_fromLargeInt",
            fn () => Word32.toString (Word32.fromLargeInt v),
            fn () => Word32.toString (Word32.fromLargeInt (I v)));
      pair ("word32_toInt",
            fn () => Int.toString (Word32.toInt w32),
            fn () => Int.toString (Word32.toInt (I w32)));
      pair ("word32_toIntX",
            fn () => Int.toString (Word32.toIntX w32),
            fn () => Int.toString (Word32.toIntX (I w32)));
      pair ("word32_toLarge",
            fn () => LargeWord.toString (Word32.toLarge w32),
            fn () => LargeWord.toString (Word32.toLarge (I w32)));
      pair ("word32_toLargeX",
            fn () => LargeWord.toString (Word32.toLargeX w32),
            fn () => LargeWord.toString (Word32.toLargeX (I w32)));
      pair ("word32_fromLarge",
            fn () => Word32.toString (Word32.fromLarge lwv),
            fn () => Word32.toString (Word32.fromLarge (I lwv)))
    end;

    (* ---- Real <-> LargeInt ------------------------------------------------- *)
    (* Real.fromLargeInt widens IntInf -> Real (rounds; never raises).           *)
    pair ("real_fromLargeInt",
          fn () => Real.toString (Real.fromLargeInt v),
          fn () => Real.toString (Real.fromLargeInt (I v)));
    (* Real.toLargeInt narrows a Real -> IntInf under a rounding mode.  Drive it
       off a Real derived from v (scaled into a representable range) so the
       rounding behaviour is exercised on a varied magnitude.  Each rounding mode. *)
    let
      val r = Real.fromLargeInt v / 7.0           (* introduces a fraction *)
      fun toLI m = LargeInt.toString (Real.toLargeInt m r)
      fun toLIx m x = LargeInt.toString (Real.toLargeInt m x)
    in
      pair ("real_toLargeInt_near",
            fn () => toLI IEEEReal.TO_NEAREST,
            fn () => toLIx IEEEReal.TO_NEAREST (I r));
      pair ("real_toLargeInt_zero",
            fn () => toLI IEEEReal.TO_ZERO,
            fn () => toLIx IEEEReal.TO_ZERO (I r));
      pair ("real_toLargeInt_posinf",
            fn () => toLI IEEEReal.TO_POSINF,
            fn () => toLIx IEEEReal.TO_POSINF (I r));
      pair ("real_toLargeInt_neginf",
            fn () => toLI IEEEReal.TO_NEGINF,
            fn () => toLIx IEEEReal.TO_NEGINF (I r))
    end
  end

val () =
  let fun loop i = if i >= nIters then () else (doIter i; loop (i + 1))
  in loop 0 end

val () = print "@@FUZZ_CONVERT_DONE=ok\n"
