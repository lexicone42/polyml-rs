(* diff-corpus FUZZ DRIVER: fuzz_int  (domain = int)  (2026-06-17)
   ================================================================
   A DETERMINISTIC differential fuzz over integer arithmetic. A hand-rolled
   LCG PRNG (seed = 0w1, see `s` below) drives operand generation; the SAME
   pure-SML code runs IDENTICALLY on upstream PolyML and on our `poly run`, so
   both consume the EXACT same random sequence and any @@<label>=<value>
   divergence is a faithfulness bug in OUR port.

   Domain: integer arithmetic across two representations and three magnitude
   classes:
     * Int / FixedInt  (63-bit fixed; Int = FixedInt in the default-int config)
       small (-100..100) and near the tagged boundary (~2^62), plus the
       OVERFLOW boundaries (maxInt+1, ~minInt, abs minInt => Overflow).
     * IntInf          (arbitrary precision; the RTS Poly*Arbitrary emulation)
       BIG boxed bignums 2^80..2^300 with random signs.

   For every operand pair and every operator we emit TWO @@cases:
     * INLINE  form  `a OP b`        — hits the bytecode opcode path.
     * REF-FORCED    `I a OP I b`    — `fun I x = let val r = ref x in !r end`
       defeats inline specialization so the op dispatches through the RTS
       arbitrary-precision path. THIS is where the PolySubtractArbitrary
       negation bug lived (rts.rs arb_binop computed op(arg2,arg1)); the
       inline opcode path was already correct, so only the ref-forced cases
       catch that class.
   Labels: @@<op>_inline_<i> and @@<op>_rts_<i>.

   Results are stringified deterministically (IntInf.toString / Int.toString /
   Bool.toString). Operators that can raise (Div, Overflow) are wrapped so an
   exception becomes a COMPARABLE VALUE ("OVF"/"DIV"/"EXN"): both sides raising
   => they agree, not a divergence.

   KNOWN stage-0 artifact: IntInf.andb/orb with a short operand in the special
   slot. This driver deliberately does NOT include bitwise ops, so no stage-0
   noise. *)

(* ----- ref-force helper: defeats inline specialization (RTS path) ----- *)
fun I x = let val r = ref x in !r end;

(* ----- the LCG (Knuth/MMIX constants); Word is 63-bit here ----- *)
val s = ref (0w1 : word);
fun step () = (s := !s * 0w6364136223846793005 + 0w1442695040888963407; !s);
(* a 52-bit nonnegative draw (drop low/high noise) *)
fun nxt () = Word.toInt (Word.>> (step (), 0w11));
(* a fresh bit *)
fun bit () = Word.toInt (Word.andb (step (), 0w1));
(* random in [0, n)  (n small) *)
fun upto n = nxt () mod n;
(* sign helpers (monomorphic — `~` defaults to int, so be explicit) *)
fun randSignI (x : IntInf.int) : IntInf.int = if bit () = 0 then x else IntInf.~ x;
fun randSignInt (x : int) : int = if bit () = 0 then x else Int.~ x;

(* ----- operand generators (return IntInf.int) ----- *)
val maxI : IntInf.int = IntInf.fromInt (valOf Int.maxInt);  (* 2^62 - 1 *)
val minI : IntInf.int = IntInf.fromInt (valOf Int.minInt);  (* ~2^62    *)

(* small operand in -100..100 *)
fun genSmall () : IntInf.int = IntInf.fromInt (randSignInt (upto 101));

(* near the 63-bit tagged boundary: within +/- a small delta of +/-2^62 and
   +/- maxInt, so + and * tip into Overflow for Int and stay representable for
   IntInf.  delta in 0..7. *)
fun genBoundary () : IntInf.int =
  let val delta = IntInf.fromInt (upto 8)
      val k = upto 4
      val base =
        case k of
            0 => maxI            (*  2^62 - 1 *)
          | 1 => minI            (* ~2^62     *)
          | 2 => IntInf.pow (2, 61)
          | _ => ~ (IntInf.pow (2, 61))
  in randSignI (base + (if bit () = 0 then delta else IntInf.~ delta)) end;

(* BIG boxed bignum: 2^e for e in 80..300, times a small odd-ish factor, random
   sign.  Always exceeds the 63-bit Int range => Int ops on these Overflow. *)
fun genBig () : IntInf.int =
  let val e = 80 + upto 221                 (* 80..300 *)
      val factor = IntInf.fromInt (1 + upto 1000)
  in randSignI (IntInf.pow (2, e) * factor) end;

(* pick a generator by class for IntInf operands *)
fun genII () : IntInf.int =
  case upto 3 of 0 => genSmall () | 1 => genBoundary () | _ => genBig ();

(* an Int-range operand (small or boundary; never a bignum), returned AS an
   `int` clamped into [minInt, maxInt] so the down-cast is always exact and the
   generator itself never raises Overflow. Boundary operands sit at/near the
   63-bit limits so + and * tip into Overflow when the ARITHMETIC overflows
   (which is the point), but the operands themselves are representable. *)
fun clampToInt (v : IntInf.int) : int =
  if v > maxI then valOf Int.maxInt
  else if v < minI then valOf Int.minInt
  else IntInf.toInt v;
fun genIntRange () : int =
  if bit () = 0 then clampToInt (genSmall ()) else clampToInt (genBoundary ());

(* ----- emit one labelled result line ----- *)
fun emit (label, v) = print ("@@" ^ label ^ "=" ^ v ^ "\n");

(* ===================================================================== *)
(* SECTION A:  IntInf arithmetic (the RTS Poly*Arbitrary emulation path)  *)
(*   big/boundary/small mix; inline AND ref-forced.                       *)
(* ===================================================================== *)

(* wrap an IntInf op that may raise Div *)
fun iiWrap f = (IntInf.toString (f ()) handle Div => "DIV" | Overflow => "OVF" | _ => "EXN");

val nII = 80;   (* operand pairs for the IntInf section *)

fun runII () =
  let
    fun loop i =
      if i >= nII then ()
      else
        let
          val a = genII ()
          val b = genII ()
          val si = Int.toString i
        in
          (* + - *  (and div/mod/quot/rem, guarding Div) for IntInf *)
          emit ("iiadd_inline_" ^ si, iiWrap (fn () => a + b));
          emit ("iiadd_rts_" ^ si,    iiWrap (fn () => I a + I b));
          emit ("iisub_inline_" ^ si, iiWrap (fn () => a - b));
          emit ("iisub_rts_" ^ si,    iiWrap (fn () => I a - I b));
          emit ("iimul_inline_" ^ si, iiWrap (fn () => a * b));
          emit ("iimul_rts_" ^ si,    iiWrap (fn () => I a * I b));
          emit ("iidiv_inline_" ^ si, iiWrap (fn () => IntInf.div (a, b)));
          emit ("iidiv_rts_" ^ si,    iiWrap (fn () => IntInf.div (I a, I b)));
          emit ("iimod_inline_" ^ si, iiWrap (fn () => IntInf.mod (a, b)));
          emit ("iimod_rts_" ^ si,    iiWrap (fn () => IntInf.mod (I a, I b)));
          emit ("iiquot_inline_" ^ si, iiWrap (fn () => IntInf.quot (a, b)));
          emit ("iiquot_rts_" ^ si,    iiWrap (fn () => IntInf.quot (I a, I b)));
          emit ("iirem_inline_" ^ si, iiWrap (fn () => IntInf.rem (a, b)));
          emit ("iirem_rts_" ^ si,    iiWrap (fn () => IntInf.rem (I a, I b)));
          emit ("iineg_inline_" ^ si, iiWrap (fn () => ~ a));
          emit ("iineg_rts_" ^ si,    iiWrap (fn () => ~ (I a)));
          emit ("iiabs_inline_" ^ si, iiWrap (fn () => IntInf.abs a));
          emit ("iiabs_rts_" ^ si,    iiWrap (fn () => IntInf.abs (I a)));
          (* comparisons: stringify the Bool *)
          emit ("iilt_inline_" ^ si, Bool.toString (a < b));
          emit ("iilt_rts_" ^ si,    Bool.toString (I a < I b));
          emit ("iile_inline_" ^ si, Bool.toString (a <= b));
          emit ("iile_rts_" ^ si,    Bool.toString (I a <= I b));
          emit ("iigt_inline_" ^ si, Bool.toString (a > b));
          emit ("iigt_rts_" ^ si,    Bool.toString (I a > I b));
          emit ("iieq_inline_" ^ si, Bool.toString (a = b));
          emit ("iieq_rts_" ^ si,    Bool.toString (I a = I b));
          emit ("iicmp_inline_" ^ si,
                (case IntInf.compare (a, b) of LESS => "LT" | EQUAL => "EQ" | GREATER => "GT"));
          emit ("iicmp_rts_" ^ si,
                (case IntInf.compare (I a, I b) of LESS => "LT" | EQUAL => "EQ" | GREATER => "GT"));
          emit ("iisign_inline_" ^ si, Int.toString (IntInf.sign a));
          emit ("iisign_rts_" ^ si,    Int.toString (IntInf.sign (I a)));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION B:  Int / FixedInt 63-bit fixed arithmetic                     *)
(*   small + boundary operands; Overflow boundaries; inline AND ref.      *)
(*   Operands are Int-range (so down-cast from IntInf is exact).          *)
(* ===================================================================== *)

(* wrap an Int op that may raise Overflow/Div *)
fun iWrap f = (Int.toString (f ()) handle Overflow => "OVF" | Div => "DIV" | _ => "EXN");

val nI = 70;   (* operand pairs for the Int section *)

fun runI () =
  let
    fun loop i =
      if i >= nI then ()
      else
        let
          val ai = genIntRange ()
          val bi = genIntRange ()
          val si = Int.toString i
        in
          emit ("iadd_inline_" ^ si, iWrap (fn () => ai + bi));
          emit ("iadd_rts_" ^ si,    iWrap (fn () => I ai + I bi));
          emit ("isub_inline_" ^ si, iWrap (fn () => ai - bi));
          emit ("isub_rts_" ^ si,    iWrap (fn () => I ai - I bi));
          emit ("imul_inline_" ^ si, iWrap (fn () => ai * bi));
          emit ("imul_rts_" ^ si,    iWrap (fn () => I ai * I bi));
          emit ("idiv_inline_" ^ si, iWrap (fn () => Int.div (ai, bi)));
          emit ("idiv_rts_" ^ si,    iWrap (fn () => Int.div (I ai, I bi)));
          emit ("imod_inline_" ^ si, iWrap (fn () => Int.mod (ai, bi)));
          emit ("imod_rts_" ^ si,    iWrap (fn () => Int.mod (I ai, I bi)));
          emit ("iquot_inline_" ^ si, iWrap (fn () => Int.quot (ai, bi)));
          emit ("iquot_rts_" ^ si,    iWrap (fn () => Int.quot (I ai, I bi)));
          emit ("irem_inline_" ^ si, iWrap (fn () => Int.rem (ai, bi)));
          emit ("irem_rts_" ^ si,    iWrap (fn () => Int.rem (I ai, I bi)));
          emit ("ineg_inline_" ^ si, iWrap (fn () => ~ ai));
          emit ("ineg_rts_" ^ si,    iWrap (fn () => ~ (I ai)));
          emit ("iabs_inline_" ^ si, iWrap (fn () => Int.abs ai));
          emit ("iabs_rts_" ^ si,    iWrap (fn () => Int.abs (I ai)));
          (* comparisons *)
          emit ("ilt_inline_" ^ si, Bool.toString (ai < bi));
          emit ("ilt_rts_" ^ si,    Bool.toString (I ai < I bi));
          emit ("ile_inline_" ^ si, Bool.toString (ai <= bi));
          emit ("ile_rts_" ^ si,    Bool.toString (I ai <= I bi));
          emit ("igt_inline_" ^ si, Bool.toString (ai > bi));
          emit ("igt_rts_" ^ si,    Bool.toString (I ai > I bi));
          emit ("ieq_inline_" ^ si, Bool.toString (ai = bi));
          emit ("ieq_rts_" ^ si,    Bool.toString (I ai = I bi));
          emit ("imin_inline_" ^ si, Int.toString (Int.min (ai, bi)));
          emit ("imax_inline_" ^ si, Int.toString (Int.max (ai, bi)));
          emit ("isgn_inline_" ^ si, Int.toString (Int.sign ai));
          loop (i + 1)
        end
  in loop 0 end;

(* ===================================================================== *)
(* SECTION C:  explicit OVERFLOW / boundary corner cases (fixed, named)   *)
(*   minInt negated / abs => Overflow; maxInt+1 => Overflow; both paths.  *)
(* ===================================================================== *)

val mxI = valOf Int.maxInt;   (*  2^62 - 1 *)
val mnI = valOf Int.minInt;   (* ~2^62     *)

fun runCorners () =
  let in
    emit ("c_maxp1_inline",  iWrap (fn () => mxI + 1));
    emit ("c_maxp1_rts",     iWrap (fn () => I mxI + I 1));
    emit ("c_minm1_inline",  iWrap (fn () => mnI - 1));
    emit ("c_minm1_rts",     iWrap (fn () => I mnI - I 1));
    emit ("c_negmin_inline", iWrap (fn () => ~ mnI));
    emit ("c_negmin_rts",    iWrap (fn () => ~ (I mnI)));
    emit ("c_absmin_inline", iWrap (fn () => Int.abs mnI));
    emit ("c_absmin_rts",    iWrap (fn () => Int.abs (I mnI)));
    emit ("c_maxtimes2_inline", iWrap (fn () => mxI * 2));
    emit ("c_maxtimes2_rts",    iWrap (fn () => I mxI * I 2));
    emit ("c_mintimes2_inline", iWrap (fn () => mnI * 2));
    emit ("c_mintimes2_rts",    iWrap (fn () => I mnI * I 2));
    (* minInt div ~1 => Overflow (the classic two's-complement corner) *)
    emit ("c_mindivm1_inline", iWrap (fn () => Int.div (mnI, ~1)));
    emit ("c_mindivm1_rts",    iWrap (fn () => Int.div (I mnI, I (~1))));
    emit ("c_minquotm1_inline", iWrap (fn () => Int.quot (mnI, ~1)));
    emit ("c_minquotm1_rts",    iWrap (fn () => Int.quot (I mnI, I (~1))));
    (* div/mod/quot/rem by zero => Div *)
    emit ("c_divz_inline", iWrap (fn () => Int.div (mxI, 0)));
    emit ("c_divz_rts",    iWrap (fn () => Int.div (I mxI, I 0)));
    emit ("c_modz_inline", iWrap (fn () => Int.mod (mxI, 0)));
    emit ("c_remz_inline", iWrap (fn () => Int.rem (mxI, 0)));
    emit ("c_quotz_inline", iWrap (fn () => Int.quot (mxI, 0)));
    (* maxInt + maxInt => Overflow; maxInt - minInt => Overflow *)
    emit ("c_maxpmax_rts", iWrap (fn () => I mxI + I mxI));
    emit ("c_maxmmin_rts", iWrap (fn () => I mxI - I mnI));
    (* IntInf has NO overflow: these must produce real bignums on both sides *)
    emit ("c_ii_maxp1", iiWrap (fn () => IntInf.fromInt mxI + 1));
    emit ("c_ii_negmin", iiWrap (fn () => ~ (IntInf.fromInt mnI)));
    emit ("c_ii_absmin", iiWrap (fn () => IntInf.abs (IntInf.fromInt mnI)));
    (* IntInf div by zero => Div *)
    emit ("c_ii_divz", iiWrap (fn () => IntInf.div (IntInf.pow (2, 80), 0)))
  end;

(* run all sections (order fixed => deterministic LCG consumption) *)
val () = runII ();
val () = runI ();
val () = runCorners ();
