(* diff-corpus: fuzz_conversions_rts.sml — DETERMINISTIC differential FUZZ DRIVER
   ==============================================================================
   Category: CONVERSIONS — the cross-cast matrix
   {Int, IntInf, Real, Real32, Word, Word8, Word32, LargeWord} via the RTS
   conversion paths, ref-forced.  This is the conversions sibling of
   fuzz_convert.sml; it deliberately TARGETS THE WATCH-LIST EDGES that a random
   magnitude sweep tends to step over:

     - IntInf.toInt / Int.fromLarge Overflow EXACTLY at maxInt/minInt +/- 1
     - Real.toLargeInt ROUND-HALF-EVEN ties (.5 / -.5 at varied magnitudes)
       under ALL FOUR IEEEReal rounding modes
     - IntInf.fromReal / Real.toLargeInt at the largest exactly-representable
       integer boundaries (2^53 region for double, 2^24 for Real32)
     - Word sign-extension: toInt (Overflow on the top bit) vs toIntX (signed)
       at the sign-bit boundary for Word / Word8 / Word32 / LargeWord
     - Real32 narrow/widen incl. SUBNORMAL round-trips (Real.fromLarge,
       Real32.toLarge, fromInt at the Real32 integer-precision boundary 2^24)

   Like its siblings, each conversion is emitted TWICE per operand:
     @@<conv>_inline_<i>  :  CONV v          (bytecode opcode path, inline-spec.)
     @@<conv>_rts_<i>     :  CONV (I v)      (ref-forced; defeats inline spec. so
                                              the conversion dispatches through the
                                              RTS Poly*Arbitrary / Float / Ldexp /
                                              GetLowOrderAsLargeWord emulation path
                                              — the surface that hid the
                                              PolySubtractArbitrary negation bug,
                                              fixed dcdbbd4).

   PRNG: the same Knuth LCG (seed 0w1) as fuzz_intinf.sml / fuzz_convert.sml.
   Word.wordSize = 63 in this FixedInt basis, so the Word multiply/add stream is
   mod 2^63 and bit-identical across our `poly run` and BOTH upstream oracles.

   DETERMINISM: outputs are Int/IntInf/Word*/LargeInt.toString, Real/Real32/
   LargeReal.toString and Bool.toString only — all PolyML's own, platform-stable
   on same-arch.  Conversions that can raise (Overflow on narrowing, Domain on
   NaN, Overflow on +/-Inf) are caught and stringified so "both sides raise" is an
   AGREEMENT, not a divergence.  Run:
       tools/diff-oracle.sh tools/diff-corpus/fuzz_conversions_rts.sml
*)

(* ------------------------------------------------------------------ PRNG --- *)
val s = ref (0w1 : Word.word)
fun nxtW () =
  ( s := !s * 0w6364136223846793005 + 0w1442695040888963407
  ; Word.>> (!s, 0w11) )                          (* a ~52-bit non-negative Word *)
fun nxt () : IntInf.int = Word.toLargeInt (nxtW ())
fun rndMod (m : IntInf.int) : IntInf.int = (nxt ()) mod m
fun rndSignII () : IntInf.int = if (nxt ()) mod 2 = 0 then 1 else ~1
fun rndSignR () : real        = if (nxt ()) mod 2 = 0 then 1.0 else ~1.0

(* ref-force: a value laundered through a ref cannot be inline-specialized by the
   compiler, so the conversion dispatches through the RTS path. *)
fun I  (x : IntInf.int)    = let val r = ref x in !r end
fun IR (x : real)          = let val r = ref x in !r end
fun I32 (x : Real32.real)  = let val r = ref x in !r end
fun IW (x : Word.word)     = let val r = ref x in !r end
fun ILW (x : LargeWord.word) = let val r = ref x in !r end

(* ------------------------------------------------------------- emit helpers --- *)
fun emit (label, value) = print ("@@" ^ label ^ "=" ^ value ^ "\n")

fun catch (th : unit -> string) : string =
  (th ()) handle Overflow => "OVF"
               | General.Domain => "DOM"
               | Div => "DIV"
               | Size => "SIZ"
               | _ => "EXN"

(* a conversion emitted in inline + ref-forced form (both see the SAME operand) *)
fun pair (nm, i, inlF, rtsF) =
  ( emit (nm ^ "_inline_" ^ Int.toString i, catch inlF)
  ; emit (nm ^ "_rts_"    ^ Int.toString i, catch rtsF) )

(* ============================================================================ *)
(* SECTION 1 — IntInf <-> Int Overflow EXACTLY at the FixedInt boundary.        *)
(* maxInt = 2^62 - 1, minInt = -2^62.  We hand-pick the operands that straddle  *)
(* the in-range/Overflow edge so the narrowing RTS path is exercised at the      *)
(* exact transition (a random sweep rarely lands ON the boundary).              *)
(* ============================================================================ *)
local
  val maxI = IntInf.pow (2, 62) - 1        (* = valOf Int.maxInt *)
  val minI = ~ (IntInf.pow (2, 62))        (* = valOf Int.minInt *)
  (* operands: max-1, max, max+1 (OVF), min+1, min, min-1 (OVF), and 0 *)
  val edges = [ maxI - 1, maxI, maxI + 1, minI + 1, minI, minI - 1, 0,
                maxI + 5, minI - 5 ]
  fun go (_, []) = ()
    | go (i, v :: rest) =
        ( pair ("intinf_toInt_edge", i,
                fn () => Int.toString (IntInf.toInt v),
                fn () => Int.toString (IntInf.toInt (I v)))
        ; pair ("int_fromLarge_edge", i,
                fn () => Int.toString (Int.fromLarge v),
                fn () => Int.toString (Int.fromLarge (I v)))
        ; go (i + 1, rest) )
in
  val () = go (0, edges)
end

(* ============================================================================ *)
(* SECTION 2 — Real.toLargeInt ROUND-HALF-EVEN ties, all four modes.            *)
(* The TO_NEAREST mode must round half-to-even (banker's rounding): 2.5 -> 2,   *)
(* 3.5 -> 4, ~2.5 -> ~2, ~3.5 -> ~4.  We feed exact .5 ties at a range of       *)
(* magnitudes (all exactly representable as doubles) plus .25/.75 quarters,     *)
(* and run all four IEEEReal modes.  This is THE round-half-even watch item.    *)
(* ============================================================================ *)
local
  (* exact-half ties: n + 0.5 for a spread of n (each exactly representable). *)
  val ties = [ 0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 10.5, 11.5, 100.5, 101.5,
               ~0.5, ~1.5, ~2.5, ~3.5, ~4.5, ~5.5, ~10.5, ~11.5,
               1048576.5, 1048577.5,           (* 2^20 + .5 region *)
               ~1048576.5, ~1048577.5,
               0.25, 0.75, 1.25, 1.75, 2.25, 2.75,
               ~0.25, ~0.75, ~2.25, ~2.75 ]
  fun toLI m x = IntInf.toString (Real.toLargeInt m x)
  fun go (_, []) = ()
    | go (i, x :: rest) =
        ( pair ("toLI_near", i, fn () => toLI IEEEReal.TO_NEAREST x,
                                fn () => toLI IEEEReal.TO_NEAREST (IR x))
        ; pair ("toLI_zero", i, fn () => toLI IEEEReal.TO_ZERO x,
                                fn () => toLI IEEEReal.TO_ZERO (IR x))
        ; pair ("toLI_posinf", i, fn () => toLI IEEEReal.TO_POSINF x,
                                  fn () => toLI IEEEReal.TO_POSINF (IR x))
        ; pair ("toLI_neginf", i, fn () => toLI IEEEReal.TO_NEGINF x,
                                  fn () => toLI IEEEReal.TO_NEGINF (IR x))
        (* round/floor/ceil/trunc -> Int (these share the same RTS realFloor/Ceil/
           Round/Trunc backing path; round must also be half-to-even).
           NB: the `round_tie` lines AGREE with our runtime AND the NATIVE upstream
           oracle (both round half-to-EVEN: Real.round 0.5 = 0), but DIVERGE from
           the bytecode-INTERP upstream oracle, whose inline Real.round opcode
           rounds half-UP (0.5 -> 1, 2.5 -> 3) — an upstream native-vs-interp
           inconsistency (its own realRound / toLargeInt stay half-to-even).  We
           match the native reference; flagged for human, not our bug.  The fence
           runs against the native oracle by default, so it stays green. *)
        ; pair ("round_tie", i, fn () => Int.toString (Real.round x),
                                fn () => Int.toString (Real.round (IR x)))
        ; pair ("floor_tie", i, fn () => Int.toString (Real.floor x),
                                fn () => Int.toString (Real.floor (IR x)))
        ; pair ("ceil_tie", i, fn () => Int.toString (Real.ceil x),
                               fn () => Int.toString (Real.ceil (IR x)))
        ; pair ("trunc_tie", i, fn () => Int.toString (Real.trunc x),
                                fn () => Int.toString (Real.trunc (IR x)))
        ; go (i + 1, rest) )
in
  val () = go (0, ties)
end

(* ============================================================================ *)
(* SECTION 3 — Real.toLargeInt / Real.fromLargeInt at large-magnitude integer   *)
(* boundaries.  Doubles are exact integers up to 2^53; beyond that the value is *)
(* the rounded representable double.  We round-trip IntInf -> Real -> IntInf at  *)
(* and beyond 2^53 to exercise the Float/toArbitrary RTS path on big magnitudes.*)
(* ============================================================================ *)
local
  val p53 = IntInf.pow (2, 53)
  val p62 = IntInf.pow (2, 62)
  (* p53 - 1 (= 2^53 - 1, an EXACT odd integer) IS now included as a fence.
     PolyRealRound (libpolyml/reals.cpp:350-359) computes `floor(arg + 0.5)`;
     arg+0.5 for an exact odd integer in [2^52, 2^53) is not representable so it
     rounds UP to the next even, then floor keeps it: upstream
     Real.toLargeInt TO_NEAREST (2^53-1) = 2^53, for EVERY odd exact integer in
     [2^52, 2^53).  Historically (pre-2026-06-20) OUR runtime used Rust
     `round_ties_even` and returned the integer UNCHANGED — i.e. we diverged
     from upstream here (a "we are more correct" asymmetry, originally flagged
     for human like the andb/orb stage-0 allow-list, task #72).  The REAL32 RTS
     differential-fuzz seat then re-wired PolyRealRound/PolyRealFRound to
     upstream's EXACT fmod/floor(arg+0.5) algorithm (rts.rs poly_real_round_f64,
     primarily to fix a sign-of-zero divergence) — which ALSO made us reproduce
     this precision behavior BIT-FOR-BIT.  So as of 2026-06-20 we are bug-for-bug
     faithful at 2^53-1 against BOTH the native and bytecode-interp oracles, and
     the operand is included to GUARD that faithfulness (verified: ours == native
     == interp == 9007199254740992 for the 2^53-1 round-trip). *)
  val bigs = [ p53 - 2, p53 - 1, p53, p53 + 1, p53 + 2,  (* the double-exact edge *)
               p62 - 1, p62, p62 + 1,                    (* the tagged boundary   *)
               IntInf.pow (2, 70), IntInf.pow (2, 100),
               ~ (p53 + 1), ~ p62, ~ (IntInf.pow (2, 90)) ]
  fun go (_, []) = ()
    | go (i, v :: rest) =
        ( (* fromLargeInt: IntInf -> Real (rounds; never raises) *)
          pair ("real_fromLI", i,
                fn () => Real.toString (Real.fromLargeInt v),
                fn () => Real.toString (Real.fromLargeInt (I v)))
        ; (* round-trip back: Real.toLargeInt o Real.fromLargeInt *)
          pair ("real_LI_RT", i,
                fn () => IntInf.toString
                           (Real.toLargeInt IEEEReal.TO_NEAREST (Real.fromLargeInt v)),
                fn () => IntInf.toString
                           (Real.toLargeInt IEEEReal.TO_NEAREST (Real.fromLargeInt (I v))))
        ; go (i + 1, rest) )
in
  val () = go (0, bigs)
end

(* ============================================================================ *)
(* SECTION 4 — Word sign-extension: toInt (Overflow if top bit set) vs toIntX   *)
(* (signed two's-complement) at the SIGN-BIT BOUNDARY for each width.  A random  *)
(* sweep rarely sets exactly the high bit; we hand-build operands straddling     *)
(* each width's sign boundary so the sign-extension RTS path is hit at the edge. *)
(* ============================================================================ *)
local
  (* Word (63-bit): sign bit = 2^62.  Word8: 2^7.  Word32: 2^31.  LargeWord: 2^63. *)
  val wEdges =
    [ 0w0, 0w1, 0w127, 0w128, 0w255, 0w256,
      Word.<< (0w1, 0w31) - 0w1, Word.<< (0w1, 0w31),       (* 2^31 +- *)
      Word.<< (0w1, 0w62) - 0w1, Word.<< (0w1, 0w62),       (* 2^62 +- : Word sign bit *)
      Word.notb 0w0 ]                                       (* all ones *)
  fun goW (_, []) = ()
    | goW (i, w :: rest) =
        ( pair ("word_toInt_edge", i,
                fn () => Int.toString (Word.toInt w),
                fn () => Int.toString (Word.toInt (IW w)))
        ; pair ("word_toIntX_edge", i,
                fn () => Int.toString (Word.toIntX w),
                fn () => Int.toString (Word.toIntX (IW w)))
        ; pair ("word_toLI_edge", i,
                fn () => LargeInt.toString (Word.toLargeInt w),
                fn () => LargeInt.toString (Word.toLargeInt (IW w)))
        ; pair ("word_toLIX_edge", i,
                fn () => LargeInt.toString (Word.toLargeIntX w),
                fn () => LargeInt.toString (Word.toLargeIntX (IW w)))
        ; goW (i + 1, rest) )

  (* LargeWord (64-bit): sign bit = 2^63. *)
  val lwEdges =
    [ 0w0, 0w1, 0w255, 0w256,
      LargeWord.<< (0w1, 0w31), LargeWord.<< (0w1, 0w31) - 0w1,
      LargeWord.<< (0w1, 0w62), LargeWord.<< (0w1, 0w63) - 0w1,
      LargeWord.<< (0w1, 0w63),                              (* 2^63 : LW sign bit *)
      LargeWord.<< (0w1, 0w63) + 0w1,
      LargeWord.notb 0w0 ]                                   (* all 64 ones *)
  fun goLW (_, []) = ()
    | goLW (i, lw :: rest) =
        ( pair ("largeword_toInt_edge", i,
                fn () => Int.toString (LargeWord.toInt lw),
                fn () => Int.toString (LargeWord.toInt (ILW lw)))
        ; pair ("largeword_toIntX_edge", i,
                fn () => Int.toString (LargeWord.toIntX lw),
                fn () => Int.toString (LargeWord.toIntX (ILW lw)))
        ; pair ("largeword_toLI_edge", i,
                fn () => LargeInt.toString (LargeWord.toLargeInt lw),
                fn () => LargeInt.toString (LargeWord.toLargeInt (ILW lw)))
        ; pair ("largeword_toLIX_edge", i,
                fn () => LargeInt.toString (LargeWord.toLargeIntX lw),
                fn () => LargeInt.toString (LargeWord.toLargeIntX (ILW lw)))
        ; goLW (i + 1, rest) )

  (* Word8 / Word32 sign-extension via toLargeX (sign-extend to 64-bit LargeWord). *)
  val w8Edges = [ 0, 1, 127, 128, 129, 254, 255 ]
  fun goW8 (_, []) = ()
    | goW8 (i, b :: rest) =
        let val w8 = Word8.fromLargeInt (IntInf.fromInt b) in
          pair ("word8_toInt_edge", i,
                fn () => Int.toString (Word8.toInt w8),
                fn () => Int.toString (Word8.toInt (let val r = ref w8 in !r end)));
          pair ("word8_toIntX_edge", i,
                fn () => Int.toString (Word8.toIntX w8),
                fn () => Int.toString (Word8.toIntX (let val r = ref w8 in !r end)));
          pair ("word8_toLarge_edge", i,
                fn () => LargeWord.toString (Word8.toLarge w8),
                fn () => LargeWord.toString (Word8.toLarge (let val r = ref w8 in !r end)));
          pair ("word8_toLargeX_edge", i,
                fn () => LargeWord.toString (Word8.toLargeX w8),
                fn () => LargeWord.toString (Word8.toLargeX (let val r = ref w8 in !r end)));
          goW8 (i + 1, rest)
        end

  val w32Edges =
    [ 0, 1, 32767, 32768, 65535, 65536,
      2147483647, 2147483648, 4294967295, 2147483646 ]      (* 2^31 +- , 2^32 - 1 *)
  fun goW32 (_, []) = ()
    | goW32 (i, n :: rest) =
        let val w32 = Word32.fromLargeInt (IntInf.fromInt n) in
          pair ("word32_toInt_edge", i,
                fn () => Int.toString (Word32.toInt w32),
                fn () => Int.toString (Word32.toInt (let val r = ref w32 in !r end)));
          pair ("word32_toIntX_edge", i,
                fn () => Int.toString (Word32.toIntX w32),
                fn () => Int.toString (Word32.toIntX (let val r = ref w32 in !r end)));
          pair ("word32_toLarge_edge", i,
                fn () => LargeWord.toString (Word32.toLarge w32),
                fn () => LargeWord.toString (Word32.toLarge (let val r = ref w32 in !r end)));
          pair ("word32_toLargeX_edge", i,
                fn () => LargeWord.toString (Word32.toLargeX w32),
                fn () => LargeWord.toString (Word32.toLargeX (let val r = ref w32 in !r end)));
          goW32 (i + 1, rest)
        end
in
  val () = goW (0, wEdges)
  val () = goLW (0, lwEdges)
  val () = goW8 (0, w8Edges)
  val () = goW32 (0, w32Edges)
end

(* ============================================================================ *)
(* SECTION 5 — Real32 narrow / widen, incl. SUBNORMAL and the integer-precision *)
(* boundary 2^24 (above which Real32 cannot represent consecutive integers).     *)
(*   Real.fromLarge IEEEReal.* : LargeReal(double) -> Real32 (narrowing, rounds) *)
(*   Real32.toLarge            : Real32 -> double  (widening, exact)             *)
(*   Real32.fromInt at/over 2^24 exercises the int->Real32 rounding path.        *)
(* ============================================================================ *)
local
  (* Real32 smallest normal ~1.1754944e-38; smallest subnormal ~1.4e-45.
     We build subnormal-range doubles and narrow them to Real32, then widen back. *)
  val subDoubles =
    [ 1.0E~40, 5.0E~44, 1.0E~45, 7.0E~46,    (* subnormal Real32 range *)
      1.1754944E~38, 1.0E~38,                 (* near smallest normal  *)
      3.4028235E38, 3.5E38,                   (* near/over Real32 max -> inf *)
      ~1.0E~40, ~5.0E~44, ~3.5E38,
      1.0E300, 0.0, ~0.0,
      16777215.0, 16777216.0, 16777217.0,     (* 2^24 -1, 2^24, 2^24 +1 *)
      ~16777217.0 ]
  fun go (_, []) = ()
    | go (i, d :: rest) =
        ( (* narrow double -> Real32 (TO_NEAREST), then widen back to double *)
          pair ("r32_narrow", i,
                fn () => Real32.toString (Real32.fromLarge IEEEReal.TO_NEAREST d),
                fn () => Real32.toString (Real32.fromLarge IEEEReal.TO_NEAREST (IR d)))
        ; pair ("r32_RT", i,
                fn () => Real.toString
                           (Real32.toLarge (Real32.fromLarge IEEEReal.TO_NEAREST d)),
                fn () => Real.toString
                           (Real32.toLarge (Real32.fromLarge IEEEReal.TO_NEAREST (IR d))))
        ; go (i + 1, rest) )

  (* Real32.fromInt at and around the 2^24 precision boundary + tagged edge. *)
  val intEdges =
    [ 16777215, 16777216, 16777217, 16777218,           (* 2^24 +- : rounding starts *)
      33554431, 33554433,                               (* 2^25 +- *)
      ~16777217, 1000000000, ~1000000000,
      4611686018427387903, ~4611686018427387904 ]       (* maxInt/minInt *)
  fun goI (_, []) = ()
    | goI (i, n :: rest) =
        let fun II x = let val r = ref x in !r end in
          pair ("r32_fromInt", i,
                fn () => Real32.toString (Real32.fromInt n),
                fn () => Real32.toString (Real32.fromInt (II n)));
          (* and the double path for the same operands *)
          pair ("real_fromInt", i,
                fn () => Real.toString (Real.fromInt n),
                fn () => Real.toString (Real.fromInt (II n)));
          goI (i + 1, rest)
        end
in
  val () = go (0, subDoubles)
  val () = goI (0, intEdges)
end

(* ============================================================================ *)
(* SECTION 6 — RANDOMIZED sweep (the fuzz part).  Draw IntInf operands across    *)
(* magnitude classes and run the full conversion family on each, ref-forced,     *)
(* so the RTS paths see a deterministic-but-varied operand stream beyond the      *)
(* hand-picked edges above.  Mirrors fuzz_convert.sml's loop but adds the         *)
(* Real.fromManAndExp (PolyRealLdexp) + Real.toLargeInt rounding matrix on a      *)
(* random fraction, and an explicit IntInf->LargeWord low-limb (the              *)
(* PolyGetLowOrderAsLargeWord path) on signed bignums.                           *)
(* ============================================================================ *)
local
  val twoPow62 = IntInf.pow (2, 62)
  fun genClassII 0 = (rndSignII ()) * (nxt () mod 101)
    | genClassII 1 = let val delta = (nxt () mod 201) - 100
                     in (rndSignII ()) * (twoPow62 + delta) end
    | genClassII _ = let val e = 80 + (IntInf.toInt (nxt () mod 221))
                         val mag = IntInf.pow (2, e) + (nxt () mod (IntInf.pow (2, 40)))
                     in (rndSignII ()) * mag end
  fun classOf () = IntInf.toInt (nxt () mod 3)
  val nIters = 24
  fun doIter i =
    let
      val v = genClassII (classOf ())
      val lwv = LargeWord.fromLargeInt v
      (* a Real with a deliberate fractional part to drive the rounding matrix *)
      val rv = Real.fromLargeInt v / 7.0
    in
      (* narrowing IntInf -> Int (Overflow off the FixedInt range) *)
      pair ("sweep_toInt", i,
            fn () => Int.toString (IntInf.toInt v),
            fn () => Int.toString (IntInf.toInt (I v)));
      (* IntInf -> Real -> IntInf round trip (TO_NEAREST) *)
      pair ("sweep_realRT", i,
            fn () => IntInf.toString
                       (Real.toLargeInt IEEEReal.TO_NEAREST (Real.fromLargeInt v)),
            fn () => IntInf.toString
                       (Real.toLargeInt IEEEReal.TO_NEAREST (Real.fromLargeInt (I v))));
      (* Real.toLargeInt rounding matrix on the fraction rv (all four modes) *)
      pair ("sweep_near", i,
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_NEAREST rv),
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_NEAREST (IR rv)));
      pair ("sweep_zero", i,
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_ZERO rv),
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_ZERO (IR rv)));
      pair ("sweep_posinf", i,
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_POSINF rv),
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_POSINF (IR rv)));
      pair ("sweep_neginf", i,
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_NEGINF rv),
            fn () => IntInf.toString (Real.toLargeInt IEEEReal.TO_NEGINF (IR rv)));
      (* Real.fromManAndExp = PolyRealLdexp.  Use v's low bits as mantissa. *)
      let val man = Real.fromLargeInt (v mod (IntInf.pow (2, 40)))
          val e = IntInf.toInt (nxt () mod 200) - 100
      in pair ("sweep_manexp", i,
               fn () => Real.toString (Real.fromManExp { man = man, exp = e }),
               fn () => Real.toString
                          (Real.fromManExp { man = IR man, exp = e }))
      end;
      (* IntInf -> LargeWord low limb (PolyGetLowOrderAsLargeWord), incl. negative *)
      pair ("sweep_lowlimb", i,
            fn () => LargeWord.toString lwv,
            fn () => LargeWord.toString (let val r = ref lwv in !r end));
      (* LargeWord -> signed LargeInt (sign-extend the 64-bit) *)
      pair ("sweep_lwToLIX", i,
            fn () => LargeInt.toString (LargeWord.toLargeIntX lwv),
            fn () => LargeInt.toString (LargeWord.toLargeIntX (ILW lwv)));
      (* IntInf -> Real32 (double-narrowing into single precision) *)
      pair ("sweep_r32", i,
            fn () => Real32.toString (Real32.fromLargeInt v),
            fn () => Real32.toString (Real32.fromLargeInt (I v)))
    end
in
  val () = let fun loop i = if i >= nIters then () else (doIter i; loop (i + 1))
           in loop 0 end
end

val () = print "@@FUZZ_CONVERSIONS_RTS_DONE=ok\n"
