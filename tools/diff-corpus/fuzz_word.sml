(* fuzz_word.sml — DETERMINISTIC differential fuzz driver (domain: word).
 *
 * A hand-rolled 64-bit LCG PRNG drives a pure-SML sequence that runs
 * IDENTICALLY on upstream PolyML and on our `poly run`, so both consume the
 * SAME random stream and any @@label divergence is a genuine faithfulness bug
 * in OUR port (NOT test nondeterminism).
 *
 * Seed: state0 = 0w1, PCG/Knuth constants (mult 0x5851F42D4C957F2D,
 *       inc 0x14057B7EF767814F). Determinism verified: identical @@lcg* on
 *       both interpreters during construction.
 *
 * DOMAIN: word — types Word (63-bit in this FixedInt basis), Word8, Word32,
 *   LargeWord (64-bit). Operators per type:
 *     arithmetic : + - * div mod      (mod/div wrapped: Div => "DIV")
 *     bitwise    : andb orb xorb notb
 *     shifts     : << >> ~>>          (shift amount swept 0 .. wordSize+2)
 *     convert    : fromInt toInt toIntX  (toInt wrapped: Overflow => "OVF")
 *     compare    : < <= = (encoded as a 3-char string)
 *
 * Each operand pair is emitted TWICE per binary op:
 *   - @@<op>_inline_<i> : `a OP b`     (hits the inline bytecode opcode path)
 *   - @@<op>_rts_<i>    : `I a OP I b` (ref-force defeats inline specialization,
 *                          dispatching through the RTS emulation path — the path
 *                          where the PolySubtractArbitrary negation bug lived).
 *
 * Bitwise on fixed-width Word is NOT the IntInf stage-0 case, so any divergence
 * here is a real opcode/RTS bug.
 *
 * Outputs are deterministic + platform-stable: only Word*.toString / Int.toString
 * / Bool.toString. No time, no addresses, no Real.
 *)

(* ----- ref-force: defeats inline specialization, routes through the RTS ----- *)
fun I x = let val r = ref x in !r end;

(* ----- the LCG: 64-bit state in a Word, advanced each draw ----- *)
val st = ref (0w1 : Word.word);
fun step () = (st := !st * 0wx5851F42D4C957F2D + 0wx14057B7EF767814F; !st);

(* a raw draw: top bits of the freshly-advanced state (best-mixed) as a Word *)
fun draw () = Word.>> (step (), 0w11);

(* a non-negative Int in [0, n) — n must be a small positive Int *)
fun rangeInt n = Word.toInt (Word.mod (draw (), Word.fromInt n));

(* an operand across magnitude classes, with a random sign. Returns an
 * IntInf.int (LargeInt) — distinct from the 63-bit default `int` in this basis,
 * so every word value derived from it goes through Word*.fromLargeInt (which
 * truncates the bignum to the type's width). Classes:
 *   0: small      -100 .. 100
 *   1: near tag    around 2^62 (the boxed/tagged boundary), +/- small jitter
 *   2: BIG bignum  2^80 .. ~2^300 via IntInf.pow with random exponent          *)
fun classInt () : IntInf.int =
  let
    val cls = rangeInt 3
    val sign : IntInf.int = if rangeInt 2 = 0 then 1 else ~1
    val mag : IntInf.int =
      case cls of
        0 => IntInf.fromInt (rangeInt 201 - 100)
      | 1 => let val jitter = IntInf.fromInt (rangeInt 2001 - 1000)
             in IntInf.pow (2, 62) + jitter end
      | _ => let val e = 80 + rangeInt 221      (* exponent 80..300 *)
                 val extra = IntInf.fromInt (rangeInt 1000000)
             in IntInf.pow (2, e) + extra end
  in
    sign * mag
  end;

(* a full-width random word value of `bits` bits, assembled from several draws so
 * the high bits are well-exercised (a single draw is only ~52 good bits). The
 * value is returned as a Word.word holding the low `bits` (caller converts). *)
fun rawBits bits =
  let
    val a = draw ()
    val b = Word.<< (draw (), 0w30)
    val c = Word.<< (draw (), 0w55)
    val full = Word.xorb (Word.xorb (a, b), c)
  in
    if bits >= Word.wordSize then full
    else Word.andb (full, Word.- (Word.<< (0w1, Word.fromInt bits), 0w1))
  end;

(* ===================================================================== *)
(* The fuzz is parameterised by a STRUCTURE matching this signature so the
 * same generator body runs for Word / Word8 / Word32 / LargeWord.          *)
(* Each type's body is written out explicitly below (no SML functor over the
 * Word structures — keeps it simple and avoids any functor-application path
 * differences); a small code generator in this file would be nicer but we
 * want the emitted sequence fixed and obvious.                              *)

(* number of operand pairs per type (4 types -> 4*N pairs; ~32 @@cases/pair) *)
val N = 60;

(* helper: bool -> "T"/"F" *)
fun bb b = if b then "T" else "F";

(* ===================== WORD (63-bit) ===================== *)
local
  fun mk () =
    let val r = rangeInt 2
    in if r = 0 then Word.fromLargeInt (classInt ()) else rawBits Word.wordSize end
  fun amt () = rangeInt (Word.wordSize + 3)   (* 0 .. wordSize+2 *)
  fun line lab v = print ("@@" ^ lab ^ "=" ^ v ^ "\n")
  fun S w = Word.toString w
  fun dv f = (f () handle Div => "DIV" | Overflow => "OVF" | _ => "EXN")
  fun runOne i =
    let
      val a = mk () val b = mk ()
      val sh = Word.fromInt (amt ())
      val k = Int.toString i
    in
      line ("w_add_inline_" ^ k) (S (Word.+ (a, b)));
      line ("w_add_rts_" ^ k)    (S (Word.+ (I a, I b)));
      line ("w_sub_inline_" ^ k) (S (Word.- (a, b)));
      line ("w_sub_rts_" ^ k)    (S (Word.- (I a, I b)));
      line ("w_mul_inline_" ^ k) (S (Word.* (a, b)));
      line ("w_mul_rts_" ^ k)    (S (Word.* (I a, I b)));
      line ("w_div_inline_" ^ k) (dv (fn () => S (Word.div (a, b))));
      line ("w_div_rts_" ^ k)    (dv (fn () => S (Word.div (I a, I b))));
      line ("w_mod_inline_" ^ k) (dv (fn () => S (Word.mod (a, b))));
      line ("w_mod_rts_" ^ k)    (dv (fn () => S (Word.mod (I a, I b))));
      line ("w_andb_inline_" ^ k) (S (Word.andb (a, b)));
      line ("w_andb_rts_" ^ k)    (S (Word.andb (I a, I b)));
      line ("w_orb_inline_" ^ k)  (S (Word.orb (a, b)));
      line ("w_orb_rts_" ^ k)     (S (Word.orb (I a, I b)));
      line ("w_xorb_inline_" ^ k) (S (Word.xorb (a, b)));
      line ("w_xorb_rts_" ^ k)    (S (Word.xorb (I a, I b)));
      line ("w_notb_inline_" ^ k) (S (Word.notb a));
      line ("w_notb_rts_" ^ k)    (S (Word.notb (I a)));
      line ("w_shl_inline_" ^ k) (S (Word.<< (a, sh)));
      line ("w_shl_rts_" ^ k)    (S (Word.<< (I a, I sh)));
      line ("w_lsr_inline_" ^ k) (S (Word.>> (a, sh)));
      line ("w_lsr_rts_" ^ k)    (S (Word.>> (I a, I sh)));
      line ("w_asr_inline_" ^ k) (S (Word.~>> (a, sh)));
      line ("w_asr_rts_" ^ k)    (S (Word.~>> (I a, I sh)));
      line ("w_toInt_" ^ k)  (dv (fn () => Int.toString (Word.toInt a)));
      line ("w_toIntX_" ^ k) (Int.toString (Word.toIntX a));
      line ("w_lt_inline_" ^ k) (bb (Word.< (a, b)));
      line ("w_lt_rts_" ^ k)    (bb (Word.< (I a, I b)));
      line ("w_le_inline_" ^ k) (bb (Word.<= (a, b)));
      line ("w_le_rts_" ^ k)    (bb (Word.<= (I a, I b)));
      line ("w_eq_inline_" ^ k) (bb (a = b));
      line ("w_eq_rts_" ^ k)    (bb (I a = I b))
    end
in
  val () = let fun loop i = if i >= N then () else (runOne i; loop (i+1)) in loop 0 end
end;

(* ===================== WORD8 (8-bit) ===================== *)
local
  fun mk () =
    let val r = rangeInt 2
    in if r = 0 then Word8.fromLargeInt (classInt ()) else Word8.fromLarge (Word.toLarge (rawBits 8)) end
  fun amt () = rangeInt 11   (* 0 .. wordSize+2 = 0..10 *)
  fun line lab v = print ("@@" ^ lab ^ "=" ^ v ^ "\n")
  fun S w = Word8.toString w
  fun dv f = (f () handle Div => "DIV" | Overflow => "OVF" | _ => "EXN")
  fun runOne i =
    let
      val a = mk () val b = mk ()
      val sh = Word.fromInt (amt ())
      val k = Int.toString i
    in
      line ("w8_add_inline_" ^ k) (S (Word8.+ (a, b)));
      line ("w8_add_rts_" ^ k)    (S (Word8.+ (I a, I b)));
      line ("w8_sub_inline_" ^ k) (S (Word8.- (a, b)));
      line ("w8_sub_rts_" ^ k)    (S (Word8.- (I a, I b)));
      line ("w8_mul_inline_" ^ k) (S (Word8.* (a, b)));
      line ("w8_mul_rts_" ^ k)    (S (Word8.* (I a, I b)));
      line ("w8_div_inline_" ^ k) (dv (fn () => S (Word8.div (a, b))));
      line ("w8_div_rts_" ^ k)    (dv (fn () => S (Word8.div (I a, I b))));
      line ("w8_mod_inline_" ^ k) (dv (fn () => S (Word8.mod (a, b))));
      line ("w8_mod_rts_" ^ k)    (dv (fn () => S (Word8.mod (I a, I b))));
      line ("w8_andb_inline_" ^ k) (S (Word8.andb (a, b)));
      line ("w8_andb_rts_" ^ k)    (S (Word8.andb (I a, I b)));
      line ("w8_orb_inline_" ^ k)  (S (Word8.orb (a, b)));
      line ("w8_orb_rts_" ^ k)     (S (Word8.orb (I a, I b)));
      line ("w8_xorb_inline_" ^ k) (S (Word8.xorb (a, b)));
      line ("w8_xorb_rts_" ^ k)    (S (Word8.xorb (I a, I b)));
      line ("w8_notb_inline_" ^ k) (S (Word8.notb a));
      line ("w8_notb_rts_" ^ k)    (S (Word8.notb (I a)));
      line ("w8_shl_inline_" ^ k) (S (Word8.<< (a, sh)));
      line ("w8_shl_rts_" ^ k)    (S (Word8.<< (I a, I sh)));
      line ("w8_lsr_inline_" ^ k) (S (Word8.>> (a, sh)));
      line ("w8_lsr_rts_" ^ k)    (S (Word8.>> (I a, I sh)));
      line ("w8_asr_inline_" ^ k) (S (Word8.~>> (a, sh)));
      line ("w8_asr_rts_" ^ k)    (S (Word8.~>> (I a, I sh)));
      line ("w8_toInt_" ^ k)  (Int.toString (Word8.toInt a));
      line ("w8_toIntX_" ^ k) (Int.toString (Word8.toIntX a));
      line ("w8_lt_inline_" ^ k) (bb (Word8.< (a, b)));
      line ("w8_lt_rts_" ^ k)    (bb (Word8.< (I a, I b)));
      line ("w8_le_inline_" ^ k) (bb (Word8.<= (a, b)));
      line ("w8_le_rts_" ^ k)    (bb (Word8.<= (I a, I b)));
      line ("w8_eq_inline_" ^ k) (bb (a = b));
      line ("w8_eq_rts_" ^ k)    (bb (I a = I b))
    end
in
  val () = let fun loop i = if i >= N then () else (runOne i; loop (i+1)) in loop 0 end
end;

(* ===================== WORD32 (32-bit) ===================== *)
local
  fun mk () =
    let val r = rangeInt 2
    in if r = 0 then Word32.fromLargeInt (classInt ()) else Word32.fromLarge (Word.toLarge (rawBits 32)) end
  fun amt () = rangeInt 35   (* 0 .. 34 *)
  fun line lab v = print ("@@" ^ lab ^ "=" ^ v ^ "\n")
  fun S w = Word32.toString w
  fun dv f = (f () handle Div => "DIV" | Overflow => "OVF" | _ => "EXN")
  fun runOne i =
    let
      val a = mk () val b = mk ()
      val sh = Word.fromInt (amt ())
      val k = Int.toString i
    in
      line ("w32_add_inline_" ^ k) (S (Word32.+ (a, b)));
      line ("w32_add_rts_" ^ k)    (S (Word32.+ (I a, I b)));
      line ("w32_sub_inline_" ^ k) (S (Word32.- (a, b)));
      line ("w32_sub_rts_" ^ k)    (S (Word32.- (I a, I b)));
      line ("w32_mul_inline_" ^ k) (S (Word32.* (a, b)));
      line ("w32_mul_rts_" ^ k)    (S (Word32.* (I a, I b)));
      line ("w32_div_inline_" ^ k) (dv (fn () => S (Word32.div (a, b))));
      line ("w32_div_rts_" ^ k)    (dv (fn () => S (Word32.div (I a, I b))));
      line ("w32_mod_inline_" ^ k) (dv (fn () => S (Word32.mod (a, b))));
      line ("w32_mod_rts_" ^ k)    (dv (fn () => S (Word32.mod (I a, I b))));
      line ("w32_andb_inline_" ^ k) (S (Word32.andb (a, b)));
      line ("w32_andb_rts_" ^ k)    (S (Word32.andb (I a, I b)));
      line ("w32_orb_inline_" ^ k)  (S (Word32.orb (a, b)));
      line ("w32_orb_rts_" ^ k)     (S (Word32.orb (I a, I b)));
      line ("w32_xorb_inline_" ^ k) (S (Word32.xorb (a, b)));
      line ("w32_xorb_rts_" ^ k)    (S (Word32.xorb (I a, I b)));
      line ("w32_notb_inline_" ^ k) (S (Word32.notb a));
      line ("w32_notb_rts_" ^ k)    (S (Word32.notb (I a)));
      line ("w32_shl_inline_" ^ k) (S (Word32.<< (a, sh)));
      line ("w32_shl_rts_" ^ k)    (S (Word32.<< (I a, I sh)));
      line ("w32_lsr_inline_" ^ k) (S (Word32.>> (a, sh)));
      line ("w32_lsr_rts_" ^ k)    (S (Word32.>> (I a, I sh)));
      line ("w32_asr_inline_" ^ k) (S (Word32.~>> (a, sh)));
      line ("w32_asr_rts_" ^ k)    (S (Word32.~>> (I a, I sh)));
      line ("w32_toInt_" ^ k)  (dv (fn () => Int.toString (Word32.toInt a)));
      line ("w32_toIntX_" ^ k) (Int.toString (Word32.toIntX a));
      line ("w32_lt_inline_" ^ k) (bb (Word32.< (a, b)));
      line ("w32_lt_rts_" ^ k)    (bb (Word32.< (I a, I b)));
      line ("w32_le_inline_" ^ k) (bb (Word32.<= (a, b)));
      line ("w32_le_rts_" ^ k)    (bb (Word32.<= (I a, I b)));
      line ("w32_eq_inline_" ^ k) (bb (a = b));
      line ("w32_eq_rts_" ^ k)    (bb (I a = I b))
    end
in
  val () = let fun loop i = if i >= N then () else (runOne i; loop (i+1)) in loop 0 end
end;

(* ===================== LARGEWORD (64-bit) ===================== *)
local
  fun mk () =
    let val r = rangeInt 2
    in if r = 0 then LargeWord.fromLargeInt (classInt ())
       else (* assemble a full 64-bit value: low 63 from a 63-bit draw, then
               randomly set the top bit so bit 63 is exercised *)
         let val lo = Word.toLarge (rawBits 63)
             val hi = if rangeInt 2 = 0 then LargeWord.<< (0w1, 0w63) else 0w0
         in LargeWord.orb (lo, hi) end
    end
  fun amt () = rangeInt 67   (* 0 .. 66 *)
  fun line lab v = print ("@@" ^ lab ^ "=" ^ v ^ "\n")
  fun S w = LargeWord.toString w
  fun dv f = (f () handle Div => "DIV" | Overflow => "OVF" | _ => "EXN")
  fun runOne i =
    let
      val a = mk () val b = mk ()
      val sh = Word.fromInt (amt ())
      val k = Int.toString i
    in
      line ("lw_add_inline_" ^ k) (S (LargeWord.+ (a, b)));
      line ("lw_add_rts_" ^ k)    (S (LargeWord.+ (I a, I b)));
      line ("lw_sub_inline_" ^ k) (S (LargeWord.- (a, b)));
      line ("lw_sub_rts_" ^ k)    (S (LargeWord.- (I a, I b)));
      line ("lw_mul_inline_" ^ k) (S (LargeWord.* (a, b)));
      line ("lw_mul_rts_" ^ k)    (S (LargeWord.* (I a, I b)));
      line ("lw_div_inline_" ^ k) (dv (fn () => S (LargeWord.div (a, b))));
      line ("lw_div_rts_" ^ k)    (dv (fn () => S (LargeWord.div (I a, I b))));
      line ("lw_mod_inline_" ^ k) (dv (fn () => S (LargeWord.mod (a, b))));
      line ("lw_mod_rts_" ^ k)    (dv (fn () => S (LargeWord.mod (I a, I b))));
      line ("lw_andb_inline_" ^ k) (S (LargeWord.andb (a, b)));
      line ("lw_andb_rts_" ^ k)    (S (LargeWord.andb (I a, I b)));
      line ("lw_orb_inline_" ^ k)  (S (LargeWord.orb (a, b)));
      line ("lw_orb_rts_" ^ k)     (S (LargeWord.orb (I a, I b)));
      line ("lw_xorb_inline_" ^ k) (S (LargeWord.xorb (a, b)));
      line ("lw_xorb_rts_" ^ k)    (S (LargeWord.xorb (I a, I b)));
      line ("lw_notb_inline_" ^ k) (S (LargeWord.notb a));
      line ("lw_notb_rts_" ^ k)    (S (LargeWord.notb (I a)));
      line ("lw_shl_inline_" ^ k) (S (LargeWord.<< (a, sh)));
      line ("lw_shl_rts_" ^ k)    (S (LargeWord.<< (I a, I sh)));
      line ("lw_lsr_inline_" ^ k) (S (LargeWord.>> (a, sh)));
      line ("lw_lsr_rts_" ^ k)    (S (LargeWord.>> (I a, I sh)));
      line ("lw_asr_inline_" ^ k) (S (LargeWord.~>> (a, sh)));
      line ("lw_asr_rts_" ^ k)    (S (LargeWord.~>> (I a, I sh)));
      line ("lw_toInt_" ^ k)  (dv (fn () => Int.toString (LargeWord.toInt a)));
      line ("lw_toIntX_" ^ k) (dv (fn () => Int.toString (LargeWord.toIntX a)));
      line ("lw_lt_inline_" ^ k) (bb (LargeWord.< (a, b)));
      line ("lw_lt_rts_" ^ k)    (bb (LargeWord.< (I a, I b)));
      line ("lw_le_inline_" ^ k) (bb (LargeWord.<= (a, b)));
      line ("lw_le_rts_" ^ k)    (bb (LargeWord.<= (I a, I b)));
      line ("lw_eq_inline_" ^ k) (bb (a = b));
      line ("lw_eq_rts_" ^ k)    (bb (I a = I b))
    end
in
  val () = let fun loop i = if i >= N then () else (runOne i; loop (i+1)) in loop 0 end
end;

(* ===================== deterministic div/mod-by-ZERO sweep ===================== *)
(* Random operands almost never land on exactly 0, so the Div-as-value path is
 * forced explicitly here (inline AND ref-forced) for every type. Both sides must
 * raise Div -> "DIV" identically. *)
local
  fun dvW f = (f () handle Div => "DIV" | _ => "EXN")
  fun gen () =
    let val a = rawBits Word.wordSize
        val a8 = Word8.fromLarge (Word.toLarge (rawBits 8))
        val a32 = Word32.fromLarge (Word.toLarge (rawBits 32))
        val alw = LargeWord.fromLarge (Word.toLarge (rawBits 63))
    in
      print ("@@w_divz_inline=" ^ dvW (fn () => Word.toString (Word.div (a, 0w0))) ^ "\n");
      print ("@@w_divz_rts="    ^ dvW (fn () => Word.toString (Word.div (I a, I 0w0))) ^ "\n");
      print ("@@w_modz_inline=" ^ dvW (fn () => Word.toString (Word.mod (a, 0w0))) ^ "\n");
      print ("@@w_modz_rts="    ^ dvW (fn () => Word.toString (Word.mod (I a, I 0w0))) ^ "\n");
      print ("@@w8_divz_inline=" ^ dvW (fn () => Word8.toString (Word8.div (a8, 0w0))) ^ "\n");
      print ("@@w8_divz_rts="    ^ dvW (fn () => Word8.toString (Word8.div (I a8, I 0w0))) ^ "\n");
      print ("@@w8_modz_inline=" ^ dvW (fn () => Word8.toString (Word8.mod (a8, 0w0))) ^ "\n");
      print ("@@w8_modz_rts="    ^ dvW (fn () => Word8.toString (Word8.mod (I a8, I 0w0))) ^ "\n");
      print ("@@w32_divz_inline=" ^ dvW (fn () => Word32.toString (Word32.div (a32, 0w0))) ^ "\n");
      print ("@@w32_divz_rts="    ^ dvW (fn () => Word32.toString (Word32.div (I a32, I 0w0))) ^ "\n");
      print ("@@w32_modz_inline=" ^ dvW (fn () => Word32.toString (Word32.mod (a32, 0w0))) ^ "\n");
      print ("@@w32_modz_rts="    ^ dvW (fn () => Word32.toString (Word32.mod (I a32, I 0w0))) ^ "\n");
      print ("@@lw_divz_inline=" ^ dvW (fn () => LargeWord.toString (LargeWord.div (alw, 0w0))) ^ "\n");
      print ("@@lw_divz_rts="    ^ dvW (fn () => LargeWord.toString (LargeWord.div (I alw, I 0w0))) ^ "\n");
      print ("@@lw_modz_inline=" ^ dvW (fn () => LargeWord.toString (LargeWord.mod (alw, 0w0))) ^ "\n");
      print ("@@lw_modz_rts="    ^ dvW (fn () => LargeWord.toString (LargeWord.mod (I alw, I 0w0))) ^ "\n")
    end
in
  val () = gen ()
end;

val () = print "@@FUZZ_WORD_DONE=1\n";
