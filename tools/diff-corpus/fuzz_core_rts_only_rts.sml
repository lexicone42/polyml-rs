(* diff-corpus: fuzz_core_rts_only_rts.sml — CORE RTS-ONLY differential fuzz (2026-06-20)
   ==========================================================================================
   SWEEP SEAT: "core-rts-only".  Target = the IntInf RTS-emulation surface, with
   PRIORITY on the RTS-ONLY ops that have NO inline-opcode twin and had therefore
   NEVER been differentially fuzzed through their RTS path:
       IntInf.gcd / IntInf.lcm   (PolyGCDArbitrary / PolyLCMArbitrary)
       IntInf.andb/orb/xorb/notb (PolyAnd/Or/XorArbitrary)
       IntInf.<<  (PolyShiftLeftArbitrary)
       IntInf.~>> (PolyShiftRightArbitrary — ARITHMETIC/floor shift)
       IntInf.compare + </>/<=/>= + sign/sameSign/min/max  (PolyCompareArbitrary)
   plus the binary arith family (add/sub/mul/div/mod/quot/rem) BOTH inline AND
   ref-forced — this is where the SubtractArbitrary-class sign bug lived (the RTS
   path computed op(arg2,arg1); fine for add/mul, WRONG for sub/div/quot/rem).

   METHOD (ref-force differential):
   - The `I` helper reads a value back out of a ref, which the compiler cannot
     inline-specialize, so the operator dispatches through the RTS Poly*Arbitrary
     emulation instead of the inline bytecode opcode.  Every operand of the
     RTS-only ops is wrapped in I() so we genuinely hit the RTS path.
   - Each binary op with an inline twin is emitted TWICE per operand pair:
         @@<op>_inline_<i> : a OP b           (bytecode opcode path)
         @@<op>_rts_<i>    : (I a) OP (I b)    (RTS emulation path)

   DETERMINISM: the LCG (seed 0w1, Knuth constants) is bit-identical on upstream
   PolyML (native + bytecode-interp) and our `poly run`, so all three consume the
   SAME random stream.  All outputs are IntInf.toString / Bool.toString only.

   FINDINGS THIS DRIVER PRODUCED (2026-06-20, core-rts-only seat):
   1. lcm SIGN bug (FIXED, rts.rs poly_lcm_arbitrary): upstream lcm = x*(y/gcd) is
      SIGNED (sign = sign(x)*sign(y)); ours returned |lcm|.  Also lcm(0,0) raises
      Div upstream (gcd=0 → 0/0); ours returned 0.  Both fixed; this driver fences
      both at exact-boundary operands.
   2. andb at the ±2^62 TAGGED BOUNDARY against a boxed operand diverges, but this
      is the KNOWN UPSTREAM STAGE-0 COMPILER BUG (task #72): the stage-0-built
      basis (/tmp/basis_loaded) mis-specializes IntInf.andb's short-circuit so it
      bypasses andbFn even when the guard is false.  The RTS function
      poly_and_arbitrary is CORRECT (verified by direct RunCall.rtsCallFull2
      dispatch + on the self-bootstrapped polyexport, both give the right answer).
      ALLOW-LISTED — this driver keeps and/or/xor operands as power-of-2 + ODD
      OFFSET (never the exact ±2^62 tag boundary, never exact powers), so the
      stage-0 mis-specialization is not triggered.
   3. UPSTREAM CRASH (their bug, NOT ours): IntInf.xorb of two EXACT-power-of-2
      operands of OPPOSITE SIGN at certain bit positions (e.g. xorb(2^127,-2^127))
      aborts upstream with an assertion failure (arb.cpp:1423 logical_long
      `sign == 0 || borrowW == 0`).  Ours computes the correct value cleanly.
      To keep this driver a usable regression fence (it must run to completion on
      BOTH upstream oracles), the and/or/xor table avoids exact powers of 2 — the
      power-of-2 + ODD OFFSET operands fully exercise the two's-complement signed
      bitwise path without tripping the upstream crash.

   So: the BITWISE table is power-of-2 + odd offset, both signs, all boxed (dodges
   #2 and #3).  The ARITH / COMPARE / GCD-LCM tables use EXACT boundaries (0, ±1,
   2^62, 2^63, 2^64, 2^80, 2^127, 2^128, 2^300, tag-edge ±1) — those neither crash
   upstream nor hit the stage-0 andb bug, and they are the SubtractArbitrary-class
   home turf + the lcm-sign fence.

   Run: tools/diff-oracle.sh tools/diff-corpus/fuzz_core_rts_only_rts.sml
*)

(* ----- ref-force: defeats inline specialization, routes through the RTS ----- *)
fun I (x : IntInf.int) = let val r = ref x in !r end

(* gcd/lcm are NOT in the SML-Basis `IntInf` structure — they live in
   `PolyML.IntInf` (InitialPolyML.ML:104-105) as rtsCallFull2 "PolyGCDArbitrary"
   / "PolyLCMArbitrary".  Bind local aliases so we can apply them to I()-wrapped
   (ref-forced) operands and genuinely dispatch the RTS path.  Type is
   LargeInt.int * LargeInt.int -> LargeInt.int, and LargeInt = IntInf here. *)
val gcdRTS : IntInf.int * IntInf.int -> IntInf.int = PolyML.IntInf.gcd
val lcmRTS : IntInf.int * IntInf.int -> IntInf.int = PolyML.IntInf.lcm

(* ----- LCG PRNG (seed 0w1, Knuth constants; mod 2^63 on this 63-bit basis) -- *)
val s = ref (0w1 : Word.word)
fun nxt () =
  ( s := !s * 0w6364136223846793005 + 0w1442695040888963407
  ; Word.toLargeInt (Word.>> (!s, 0w11)) )    (* non-negative ~52-bit IntInf *)

fun rndMod (m : IntInf.int) : IntInf.int = (nxt ()) mod m
fun rndSign () : IntInf.int = if (nxt ()) mod 2 = 0 then 1 else ~1

(* ----- emit + exception->value wrapping (both-raise = agreement) ----- *)
fun emit (label, value) = print ("@@" ^ label ^ "=" ^ value ^ "\n")
fun sI (th : unit -> IntInf.int) : string =
  (IntInf.toString (th ())) handle Div => "DIV"
                                 | Overflow => "OVF"
                                 | Domain => "DOM"
                                 | _ => "EXN"
fun sB (th : unit -> bool) : string =
  (Bool.toString (th ())) handle _ => "EXN"
fun sO (th : unit -> order) : string =
  (case th () of LESS => "L" | EQUAL => "E" | GREATER => "G") handle _ => "X"
fun sInt (th : unit -> int) : string =
  (Int.toString (th ())) handle Overflow => "OVF" | _ => "EXN"

(* shared deterministic label counter *)
val ctr = ref 0
fun tick () = let val c = !ctr in (ctr := c + 1; Int.toString c) end
fun forEach _ [] = ()
  | forEach f (x :: xs) = (f x; forEach f xs)
fun allPairs f xs = forEach (fn a => forEach (fn b => f (a, b)) xs) xs

(* ----- the powers ----- *)
val p62  = IntInf.pow (2, 62)
val p63  = IntInf.pow (2, 63)
val p64  = IntInf.pow (2, 64)
val p80  = IntInf.pow (2, 80)
val p100 = IntInf.pow (2, 100)
val p127 = IntInf.pow (2, 127)
val p128 = IntInf.pow (2, 128)
val p200 = IntInf.pow (2, 200)
val p300 = IntInf.pow (2, 300)

(* =====================================================================
   PART 1 — ARITHMETIC + COMPARE + GCD/LCM at EXACT boundaries
   (the SubtractArbitrary-class home turf + the lcm-sign fence)
   ===================================================================== *)
val exactTbl : IntInf.int list =
  [ 0, 1, ~1, 2, ~2, 100, ~100,
    p62, ~p62, p62 + 1, p62 - 1, ~(p62 + 1), ~(p62 - 1),
    p63, ~p63, p64, ~p64,
    p80, ~p80, p80 + 12345, ~(p80 + 12345),
    p127, ~p127, p128, ~p128,
    p300, ~p300 ]

fun arithPair (a, b) =
  let
    val k = tick ()
    val d = if b = 0 then 1 else b   (* nonzero divisor (else uninformative Div on both) *)
  in
    emit ("add_inline_" ^ k, sI (fn () => a + b));
    emit ("add_rts_" ^ k,    sI (fn () => (I a) + (I b)));
    emit ("sub_inline_" ^ k, sI (fn () => a - b));
    emit ("sub_rts_" ^ k,    sI (fn () => (I a) - (I b)));
    emit ("subR_inline_" ^ k, sI (fn () => b - a));      (* other order — the bug's home turf *)
    emit ("subR_rts_" ^ k,    sI (fn () => (I b) - (I a)));
    emit ("mul_inline_" ^ k, sI (fn () => a * b));
    emit ("mul_rts_" ^ k,    sI (fn () => (I a) * (I b)));
    emit ("div_inline_" ^ k, sI (fn () => a div d));
    emit ("div_rts_" ^ k,    sI (fn () => (I a) div (I d)));
    emit ("mod_inline_" ^ k, sI (fn () => a mod d));
    emit ("mod_rts_" ^ k,    sI (fn () => (I a) mod (I d)));
    emit ("quot_inline_" ^ k, sI (fn () => IntInf.quot (a, d)));
    emit ("quot_rts_" ^ k,    sI (fn () => IntInf.quot (I a, I d)));
    emit ("rem_inline_" ^ k, sI (fn () => IntInf.rem (a, d)));
    emit ("rem_rts_" ^ k,    sI (fn () => IntInf.rem (I a, I d)))
  end

fun cmpPair (a, b) =
  let val k = tick () in
    emit ("cmp_rts_" ^ k,  sO (fn () => IntInf.compare (I a, I b)));
    emit ("lt_rts_" ^ k,   sB (fn () => (I a) < (I b)));
    emit ("le_rts_" ^ k,   sB (fn () => (I a) <= (I b)));
    emit ("gt_rts_" ^ k,   sB (fn () => (I a) > (I b)));
    emit ("ge_rts_" ^ k,   sB (fn () => (I a) >= (I b)));
    emit ("eq_rts_" ^ k,   sB (fn () => (I a) = (I b)));
    emit ("lt_inline_" ^ k, sB (fn () => a < b));
    emit ("le_inline_" ^ k, sB (fn () => a <= b));
    emit ("min_rts_" ^ k,  sI (fn () => IntInf.min (I a, I b)));
    emit ("max_rts_" ^ k,  sI (fn () => IntInf.max (I a, I b)));
    emit ("ssign_rts_" ^ k, sB (fn () => IntInf.sameSign (I a, I b)))
  end

(* gcd/lcm at exact boundaries (no upstream crash here; lcm sign + lcm(0,0)=Div) *)
fun glPair (a, b) =
  let val k = tick () in
    emit ("gcd_rts_" ^ k, sI (fn () => gcdRTS (I a, I b)));
    emit ("lcm_rts_" ^ k, sI (fn () => lcmRTS (I a, I b)))
  end

val () = allPairs arithPair exactTbl
val () = allPairs cmpPair   exactTbl
val () = allPairs glPair    exactTbl

(* unary at exact boundaries: sign / abs / neg (NOT notb — see PART 2) *)
fun unaryExact x =
  let val k = tick () in
    emit ("sign_rts_" ^ k, sInt (fn () => IntInf.sign (I x)));
    emit ("abs_rts_" ^ k,  sI (fn () => IntInf.abs (I x)));
    emit ("neg_rts_" ^ k,  sI (fn () => ~ (I x)))
  end
val () = forEach unaryExact exactTbl

(* =====================================================================
   PART 2 — BITWISE and/or/xor/notb  (power-of-2 + ODD OFFSET, both signs)
   Avoids: (a) the ±2^62 tagged-boundary stage-0 andb bug (task #72), and
           (b) the exact-power-of-2 opposite-sign xorb UPSTREAM CRASH.
   Still fully exercises the two's-complement SIGNED boxed bitwise path.
   ===================================================================== *)
val bitTbl : IntInf.int list =
  [ p63 + 5,  ~(p63 + 5),
    p64 + 255, ~(p64 + 255),
    p80 + 13,  ~(p80 + 13),
    p100 + 7,  ~(p100 + 7),
    p128 + 18446744073709551615, ~(p128 + 18446744073709551615),  (* + (2^64-1) *)
    p200 + 3,  ~(p200 + 3) ]

fun bitPair (a, b) =
  let val k = tick () in
    emit ("andb_rts_" ^ k, sI (fn () => IntInf.andb (I a, I b)));
    emit ("orb_rts_" ^ k,  sI (fn () => IntInf.orb (I a, I b)));
    emit ("xorb_rts_" ^ k, sI (fn () => IntInf.xorb (I a, I b)))
  end
val () = allPairs bitPair bitTbl
val () = forEach (fn x => emit ("notb_rts_" ^ tick (), sI (fn () => IntInf.notb (I x)))) bitTbl

(* =====================================================================
   PART 3 — SHIFTS (PolyShiftLeftArbitrary / PolyShiftRightArbitrary)
   shiftR is ARITHMETIC (floor toward -inf): a negative shifted far right → ~1.
   Sweep shift amount 0..wordSize+8 AND a FAR amount (200) over small/big +ve/-ve.
   ===================================================================== *)
val shiftVals : IntInf.int list =
  [ 0, 1, ~1, 7, ~7, 255, ~255,
    p62, ~p62, p62 + 1, ~(p62 + 1),
    p64 + 123, ~(p64 + 123),
    p80, ~p80, p128 + 999, ~(p128 + 999), p300, ~p300 ]
val shiftAmts : int list = [ 0, 1, 2, 31, 32, 33, 62, 63, 64, 65, 71, 200 ]

fun shiftSweep v =
  forEach (fn amt =>
    let val k = tick ()
        val w : Word.word = Word.fromInt amt
    in
      emit ("shl_rts_" ^ k, sI (fn () => IntInf.<< (I v, w)));
      emit ("asr_rts_" ^ k, sI (fn () => IntInf.~>> (I v, w)))
    end) shiftAmts
val () = forEach shiftSweep shiftVals

(* PolyGetLowOrderAsLargeWord via IntInf -> LargeWord low limb, on +ve/-ve + carries *)
fun lowWord v =
  let val k = tick () in
    emit ("lowlw_rts_" ^ k,
          (LargeWord.toString (LargeWord.fromLargeInt (I v))) handle _ => "EXN")
  end
val () = forEach lowWord shiftVals

(* =====================================================================
   PART 4 — RANDOM FUZZ (LCG-driven, classes straddling the tag boundary)
   ===================================================================== *)
val twoPow62 = p62
fun genSmall () : IntInf.int = (rndSign ()) * (rndMod 101)            (* -100..100 *)
fun genBoundary () : IntInf.int =
  let val delta = (rndMod 201) - 100 in (rndSign ()) * (twoPow62 + delta) end
fun genBig () : IntInf.int =
  let val e = 80 + (IntInf.toInt (rndMod 221))
      val mag = IntInf.pow (2, e) + (rndMod (IntInf.pow (2, 40)))
  in (rndSign ()) * mag end
fun genClass 0 = genSmall ()
  | genClass 1 = genBoundary ()
  | genClass _ = genBig ()
fun classOf () = IntInf.toInt (rndMod 3)

(* a BOXED operand whose magnitude is NOT an exact power of 2 (odd low noise) and
   strictly above the tag boundary — keeps the bitwise fuzz off the stage-0 andb
   case AND off the exact-power xorb upstream crash. *)
fun genBoxedOdd () : IntInf.int =
  let val e = 80 + (IntInf.toInt (rndMod 221))
      val noise = (rndMod (IntInf.pow (2, 40))) * 2 + 1     (* always odd, >0 *)
  in (rndSign ()) * (IntInf.pow (2, e) + noise) end

val nIters = 16
fun doIter i =
  let
    val a  = genClass (classOf ())
    val b  = genClass (classOf ())
    val d  = let val v = genClass (classOf ()) in if v = 0 then 1 else v end
    val ba = genBoxedOdd ()
    val bb = genBoxedOdd ()
    val si = Int.toString i
  in
    emit ("fadd_inline_" ^ si, sI (fn () => a + b));
    emit ("fadd_rts_" ^ si,    sI (fn () => (I a) + (I b)));
    emit ("fsub_inline_" ^ si, sI (fn () => a - b));
    emit ("fsub_rts_" ^ si,    sI (fn () => (I a) - (I b)));
    emit ("fmul_inline_" ^ si, sI (fn () => a * b));
    emit ("fmul_rts_" ^ si,    sI (fn () => (I a) * (I b)));
    emit ("fdiv_inline_" ^ si, sI (fn () => a div d));
    emit ("fdiv_rts_" ^ si,    sI (fn () => (I a) div (I d)));
    emit ("fmod_inline_" ^ si, sI (fn () => a mod d));
    emit ("fmod_rts_" ^ si,    sI (fn () => (I a) mod (I d)));
    emit ("fquot_rts_" ^ si,   sI (fn () => IntInf.quot (I a, I d)));
    emit ("frem_rts_" ^ si,    sI (fn () => IntInf.rem (I a, I d)));
    (* RTS-only ops on boxed-odd random operands *)
    emit ("fgcd_rts_" ^ si, sI (fn () => gcdRTS (I ba, I bb)));
    emit ("flcm_rts_" ^ si, sI (fn () => lcmRTS (I ba, I bb)));
    emit ("fandb_rts_" ^ si, sI (fn () => IntInf.andb (I ba, I bb)));
    emit ("forb_rts_" ^ si,  sI (fn () => IntInf.orb (I ba, I bb)));
    emit ("fxorb_rts_" ^ si, sI (fn () => IntInf.xorb (I ba, I bb)));
    emit ("fnotb_rts_" ^ si, sI (fn () => IntInf.notb (I ba)));
    emit ("fcmp_rts_" ^ si,  sO (fn () => IntInf.compare (I a, I b)));
    let val sh = Word.fromInt (IntInf.toInt (rndMod 72)) in
      emit ("fshl_rts_" ^ si, sI (fn () => IntInf.<< (I ba, sh)));
      emit ("fasr_rts_" ^ si, sI (fn () => IntInf.~>> (I ba, sh)))
    end
  end

val () =
  let fun loop i = if i >= nIters then () else (doIter i; loop (i + 1))
  in loop 0 end

val () = print "@@DONE=ok\n"
