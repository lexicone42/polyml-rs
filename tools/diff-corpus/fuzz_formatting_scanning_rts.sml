(* diff-corpus: fuzz_formatting_scanning_rts.sml — DETERMINISTIC FUZZ DRIVER (2026-06-20)
   ==============================================================================
   CATEGORY: FORMATTING / SCANNING via the RTS arbitrary-precision path.

   Domain: number<->string conversion — IntInf/Int/Word .toString / .fmt (all
   four radices) and .scan / .fromString, plus Real.toString / Real.fmt /
   Real.fromString — with a ROUNDTRIP identity discipline (toString then
   fromString/scan must recover the original value).

   WHY ref-force matters here.  Int/Word/IntInf toString+scan+fromString are PURE
   SML basis (no single Poly*ToString RTS call), BUT the SML formatting loop is
   built out of arbitrary-precision arithmetic (repeated `quot`/`rem` by the radix
   to peel digits; `*radix + digit` to accumulate on scan).  When the operand is a
   boxed bignum, those inner quot/rem/mul/add dispatch through the RTS
   Poly{QuotRemArbitraryPair,Multiply,Add,...}Arbitrary emulation.  Wrapping every
   operand in the ref-force `I` (a value read back out of a ref cannot be
   inline-specialized / const-folded by the compiler) forces the bignum operand to
   stay boxed across the whole format/scan loop, so the RTS digit-peeling path is
   exercised — exactly the surface that is otherwise only hit on the inline opcode
   path.  THIS is the analogue of the PolySubtractArbitrary negation bug (Test101,
   dcdbbd4): a value-bug that lived ONLY in the RTS emulation, invisible to the
   inline-path corpus for years.

   PRNG: the Knuth/PCG LCG on a Word.word (FixedInt basis: Word.wordSize = 63, so
   Word multiply/add is mod 2^63 — deterministic + bit-identical on upstream
   PolyML and on our `poly run`).  SEED 0w1 (fixed) => byte-identical corpus.

   For each operand we emit BOTH forms:
     @@<op>_inline_<i>  :  CONV v          — bytecode opcode path (inline spec.)
     @@<op>_rts_<i>     :  CONV (I v)      — ref-forced; RTS arbitrary-precision
                                             digit-peel / accumulate path.
   And for roundtrips:
     @@<op>_rt_<i>      :  Bool.toString (fromString (toString (I v)) = SOME (I v))

   Exceptions (Overflow on Int.scan narrowing, etc.) are caught + stringified to a
   comparable VALUE so "both sides raise" is AGREEMENT, not divergence.

   Outputs are deterministic + platform-stable: only IntInf/Int/Word*.toString,
   Bool.toString, and (for the Real roundtrip) Real.toString — all PolyML's own,
   byte-identical on same-arch upstream + ours.  Run:
       tools/diff-oracle.sh tools/diff-corpus/fuzz_formatting_scanning_rts.sml
*)

(* ------------------------------------------------------------------ PRNG --- *)
val s = ref (0w1 : Word.word)
fun nxtW () =
  ( s := !s * 0w6364136223846793005 + 0w1442695040888963407
  ; Word.>> (!s, 0w11) )                          (* a ~52-bit non-negative Word *)
fun nxt () : IntInf.int = Word.toLargeInt (nxtW ())

(* ref-force: a value read out of a ref cannot be inline-specialized, so the
   conversion's inner arithmetic dispatches through the RTS path. *)
fun I (x : IntInf.int) = let val r = ref x in !r end
fun IW (x : word)      = let val r = ref x in !r end

fun rndMod (m : IntInf.int) : IntInf.int = (nxt ()) mod m
fun rndSign () : IntInf.int = if (nxt ()) mod 2 = 0 then 1 else ~1

(* ------------------------------------------------------ operand generation --- *)
(* Magnitude classes straddling the FixedInt tag boundary (2^62) so the format /
   scan loops see small (tagged), boundary, and boxed-bignum operands. *)
val twoPow62 = IntInf.pow (2, 62)

fun genSmall ()    : IntInf.int = (rndSign ()) * (rndMod 101)             (* -100..100 *)
fun genBoundary () : IntInf.int =
  let val delta = (rndMod 201) - 100 in (rndSign ()) * (twoPow62 + delta) end
fun genBig () : IntInf.int =
  let val e   = 80 + (IntInf.toInt (rndMod 221))                          (* exp 80..300 *)
      val mag = IntInf.pow (2, e) + (rndMod (IntInf.pow (2, 40)))
  in (rndSign ()) * mag end

fun genClass 0 = genSmall ()
  | genClass 1 = genBoundary ()
  | genClass _ = genBig ()

fun classOf () : int = IntInf.toInt (rndMod 3)   (* 0,1,2 *)

(* ------------------------------------------------------------- emit helpers --- *)
fun emit (label, value) = print ("@@" ^ label ^ "=" ^ value ^ "\n")
fun istr (i : int) = Int.toString i

fun catch (th : unit -> string) : string =
  (th ()) handle Overflow => "OVF"
               | Domain   => "DOM"
               | Div      => "DIV"
               | Size     => "SIZ"
               | _        => "EXN"

(* radix list for the .fmt / .scan sweep *)
val radices = [StringCvt.BIN, StringCvt.OCT, StringCvt.DEC, StringCvt.HEX]
fun radixName StringCvt.BIN = "bin"
  | radixName StringCvt.OCT = "oct"
  | radixName StringCvt.DEC = "dec"
  | radixName StringCvt.HEX = "hex"

(* ============================ IntInf format / scan / roundtrip ============= *)
(* IntInf.fmt across all four radices, inline + ref-forced.  Then a roundtrip:
   parse the formatted string back with IntInf.scan in the SAME radix and check
   it recovers the original value.  IntInf never overflows on scan, so the
   roundtrip should always be true on both sides. *)
val nIters = 24

fun doIntInf (i : int) =
  let
    val c   = classOf ()
    val v   = genClass c
    val si  = istr i
  in
    (* plain toString, both forms *)
    emit ("ii_toString_inline_" ^ si, IntInf.toString v);
    emit ("ii_toString_rts_"    ^ si, IntInf.toString (I v));
    (* fmt across radices, both forms, + roundtrip via scanString o fmt *)
    app (fn rdx =>
      let
        val rn  = radixName rdx
        val sInl = IntInf.fmt rdx v
        val sRts = IntInf.fmt rdx (I v)
      in
        emit ("ii_fmt_" ^ rn ^ "_inline_" ^ si, sInl);
        emit ("ii_fmt_" ^ rn ^ "_rts_"    ^ si, sRts);
        (* roundtrip: scan the ref-forced-formatted string, compare to v *)
        emit ("ii_rt_" ^ rn ^ "_" ^ si,
              catch (fn () =>
                Bool.toString
                  (StringCvt.scanString (IntInf.scan rdx) sRts = SOME (I v))))
      end) radices
  end

(* ============================ Int (FixedInt) format / scan / roundtrip ===== *)
(* Int is 63-bit FixedInt here.  Int.scan can OVERFLOW (the value-relevant RTS
   path: scan accumulates val*radix + digit through the arbitrary path before the
   final narrow).  Drive Int.fmt/scan on operands that straddle Int.maxInt. *)
fun doInt (i : int) =
  let
    val c   = classOf ()
    val vII = genClass c
    (* an honest 63-bit Int derived by narrowing vII into range, plus the raw
       (possibly out-of-range) string form to exercise scan overflow. *)
    val si  = istr i
    val inRange =
      IntInf.toInt (vII mod (IntInf.pow (2, 60)) - IntInf.pow (2, 59))  (* fits Int *)
  in
    (* Int.fmt across radices on the in-range value, inline + ref-forced. *)
    app (fn rdx =>
      let val rn = radixName rdx in
        emit ("int_fmt_" ^ rn ^ "_inline_" ^ si,
              catch (fn () => Int.fmt rdx inRange));
        emit ("int_fmt_" ^ rn ^ "_rts_" ^ si,
              catch (fn () => Int.fmt rdx (IntInf.toInt (I (IntInf.fromInt inRange)))));
        (* roundtrip: Int.scan o Int.fmt should be identity on in-range ints *)
        emit ("int_rt_" ^ rn ^ "_" ^ si,
              catch (fn () =>
                Bool.toString
                  (StringCvt.scanString (Int.scan rdx) (Int.fmt rdx inRange)
                     = SOME inRange)))
      end) radices;
    (* scan a DECIMAL rendering of the full (possibly out-of-FixedInt-range)
       bignum: should overflow exactly when |vII| > Int.maxInt, on both sides. *)
    let val dec = IntInf.toString vII in
      emit ("int_scan_dec_" ^ si,
            catch (fn () =>
              case StringCvt.scanString (Int.scan StringCvt.DEC) dec of
                  SOME n => Int.toString n
                | NONE   => "NONE"))
    end
  end

(* ============================ Word format / scan / roundtrip =============== *)
(* Word.fmt / Word.scan across radices.  Word is unsigned 63-bit; the scan
   accumulation likewise runs through the arbitrary path under ref-force. *)
fun doWord (i : int) =
  let
    val c   = classOf ()
    val vII = genClass c
    val w   = Word.fromLargeInt vII          (* low 63 bits, unsigned *)
    val si  = istr i
  in
    emit ("word_toString_inline_" ^ si, Word.toString w);
    emit ("word_toString_rts_"    ^ si, Word.toString (IW w));
    app (fn rdx =>
      let
        val rn   = radixName rdx
        val sInl = Word.fmt rdx w
        val sRts = Word.fmt rdx (IW w)
      in
        emit ("word_fmt_" ^ rn ^ "_inline_" ^ si, sInl);
        emit ("word_fmt_" ^ rn ^ "_rts_"    ^ si, sRts);
        emit ("word_rt_" ^ rn ^ "_" ^ si,
              catch (fn () =>
                Bool.toString
                  (StringCvt.scanString (Word.scan rdx) sRts = SOME (IW w))))
      end) radices
  end

(* ============================ scan EDGE inputs (RTS accumulate path) ======= *)
(* Hand-picked tricky scan inputs that exercise the accumulate-into-bignum path:
   leading whitespace, sign markers, radix prefixes, leading zeros, trailing
   garbage, empty, the 0x-only stub, over/under FixedInt range, and very long
   digit strings (force the bignum accumulate).  IntInf.scan never overflows;
   Int.scan overflows past FixedInt; both must agree with upstream. *)
val scanEdges =
  [ ("ws_dec",      StringCvt.DEC, "   12345"),
    ("plus",        StringCvt.DEC, "+777"),
    ("tilde",       StringCvt.DEC, "~777"),
    ("leadzero",    StringCvt.DEC, "00000042"),
    ("trailing",    StringCvt.DEC, "99bottles"),
    ("empty",       StringCvt.DEC, ""),
    ("garbage",     StringCvt.DEC, "xyzzy"),
    ("hex_0x",      StringCvt.HEX, "0xDEADBEEF"),
    ("hex_0x_only", StringCvt.HEX, "0x"),
    ("hex_lower",   StringCvt.HEX, "deadbeef"),
    ("hex_bare",    StringCvt.HEX, "FF"),
    ("oct_8",       StringCvt.OCT, "8"),
    ("bin_2",       StringCvt.BIN, "2"),
    ("bin_long",    StringCvt.BIN, "1010101010101010101010101010101010101010101010101010101010101010101010"),
    ("dec_long",    StringCvt.DEC, "123456789012345678901234567890123456789012345678901234567890"),
    ("dec_neglong", StringCvt.DEC, "~123456789012345678901234567890123456789012345678901234567890") ]

val () =
  app (fn (nm, rdx, str) =>
    (* IntInf.scan (never overflows) — the bignum accumulate path *)
    ( emit ("scanII_" ^ nm,
            catch (fn () =>
              case StringCvt.scanString (IntInf.scan rdx) str of
                  SOME n => IntInf.toString n | NONE => "NONE"))
    (* Int.scan (overflows past FixedInt) — narrowing after accumulate *)
    ; emit ("scanInt_" ^ nm,
            catch (fn () =>
              case StringCvt.scanString (Int.scan rdx) str of
                  SOME n => Int.toString n | NONE => "NONE"))
    (* fromString convenience (DEC only, no prefix handling for non-DEC) *)
    ; emit ("fromII_" ^ nm,
            catch (fn () =>
              case IntInf.fromString str of
                  SOME n => IntInf.toString n | NONE => "NONE")) ))
    scanEdges

(* ============================ Real.toString / fmt / fromString roundtrip == *)
(* Real formatting is platform-stable on same-arch.  We ref-force the Real
   operand and check toString and a FIX/SCI/GEN fmt sweep, plus the
   toString->fromString roundtrip (Real.fromString should recover a value that
   re-stringifies identically — we compare the RE-stringified forms, which is the
   robust byte-stable identity rather than bit-exact Real = which can differ on
   nan).  Operands are derived deterministically from the PRNG. *)
fun IR (x : real) = let val r = ref x in !r end

fun randReal () : real =
  let val tag = IntInf.toInt (rndMod 8) in
    if tag = 0 then 0.0
    else if tag = 1 then ~0.0
    else
      let
        val man = Real.fromLargeInt (1 + rndMod 2000000000)
        val e   = IntInf.toInt (rndMod 240) - 120
        val sgn = Real.fromLargeInt (rndSign ())
      in sgn * Real.fromManExp { man = man, exp = e } end
  end

val rs = Real.toString

fun doReal (i : int) =
  let
    val v  = randReal ()
    val si = istr i
  in
    emit ("real_toString_inline_" ^ si, rs v);
    emit ("real_toString_rts_"    ^ si, rs (IR v));
    emit ("real_fmt_fix6_inline_" ^ si, Real.fmt (StringCvt.FIX (SOME 6)) v);
    emit ("real_fmt_fix6_rts_"    ^ si, Real.fmt (StringCvt.FIX (SOME 6)) (IR v));
    emit ("real_fmt_sci6_inline_" ^ si, Real.fmt (StringCvt.SCI (SOME 6)) v);
    emit ("real_fmt_sci6_rts_"    ^ si, Real.fmt (StringCvt.SCI (SOME 6)) (IR v));
    emit ("real_fmt_gen_inline_"  ^ si, Real.fmt (StringCvt.GEN NONE) v);
    emit ("real_fmt_gen_rts_"     ^ si, Real.fmt (StringCvt.GEN NONE) (IR v));
    (* roundtrip: fromString o toString must re-stringify identically *)
    emit ("real_rt_" ^ si,
          catch (fn () =>
            let val str = rs (IR v) in
              case Real.fromString str of
                  SOME back => Bool.toString (rs back = str)
                | NONE      => "NONE"
            end))
  end

(* ------------------------------------------------------------ run the sweep --- *)
val () =
  let fun loop f i = if i >= nIters then () else (f i; loop f (i + 1)) in
    loop doIntInf 0;
    loop doInt 0;
    loop doWord 0;
    loop doReal 0
  end

val () = print "@@FUZZ_FORMATTING_SCANNING_DONE=ok\n"
