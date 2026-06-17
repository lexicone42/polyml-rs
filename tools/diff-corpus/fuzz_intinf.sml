(* diff-corpus: fuzz_intinf.sml — DETERMINISTIC differential FUZZ DRIVER (2026-06-17)
   ==============================================================================
   Domain: IntInf.int arithmetic, division family, sign/abs/min/max, comparisons,
   and IntInf.pow.  This is a *fuzz* driver: a hand-rolled 64-bit-style LCG PRNG
   (seeded below) drives operand generation so the byte stream of random numbers
   is IDENTICAL on upstream PolyML and on our `poly run` — both interpreters
   consume the SAME random sequence and must therefore produce identical @@values.
   Any divergence is a faithfulness bug in OUR port.

   PRNG: the classic Knuth/PCG LCG constants on a Word.word (63-bit FixedInt
   basis: Word.wordSize = 63, so Word multiply/add is mod 2^63 — still a perfectly
   deterministic full-period-ish generator that is bit-identical on both sides).
       s := s*6364136223846793005 + 1442695040888963407   (mod 2^63)
   We take the high bits (>> 11) as the raw draw, then map into magnitude classes.

   SEED: 0w1 (fixed).  Re-running gives the byte-identical corpus every time.

   For each operand pair (a,b) and each operator we emit TWO cases:
     @@<op>_inline_<i>  :  a OP b            — bytecode opcode path (inline spec.)
     @@<op>_rts_<i>     :  (I a) OP (I b)    — ref-forced; defeats inline
                                               specialization so the op dispatches
                                               through the RTS Poly*Arbitrary
                                               emulation.  THIS is the path where
                                               the PolySubtractArbitrary negation
                                               bug lived (Tests/Test101, fixed
                                               dcdbbd4) — see
                                               docs/upstream-testsuite-findings-2026-06-17.md.

   Exceptions (Div, Overflow, ...) are caught and stringified to a VALUE so that
   "both sides raise" is an AGREEMENT, not a divergence.

   Outputs are fully deterministic + platform-stable: IntInf.toString / Bool.toString
   only (no Real, no time, no addresses).  Run:
       tools/diff-oracle.sh tools/diff-corpus/fuzz_intinf.sml
*)

(* ------------------------------------------------------------------ PRNG --- *)
val s = ref (0w1 : Word.word)
fun nxt () =
  ( s := !s * 0w6364136223846793005 + 0w1442695040888963407
  ; Word.toLargeInt (Word.>> (!s, 0w11)) )   (* a non-negative ~52-bit IntInf *)

(* ref-force: a value read back out of a ref cannot be inline-specialized by the
   compiler, so the operator dispatches through the RTS arbitrary-precision path. *)
fun I (x : IntInf.int) = let val r = ref x in !r end

(* a draw reduced into 0..(m-1) *)
fun rndMod (m : IntInf.int) : IntInf.int = (nxt ()) mod m

(* a random sign: 1 or ~1 *)
fun rndSign () : IntInf.int = if (nxt ()) mod 2 = 0 then 1 else ~1

(* ------------------------------------------------------ operand generation --- *)
(* Magnitude classes.  Each returns a (possibly signed) IntInf.int.
   class 0: small         -100 .. 100
   class 1: near tagged boundary   ~2^62 +/- small        (FixedInt tag edge)
   class 2: big boxed bignum       2^80 .. 2^300, random sign
*)
val twoPow62 = IntInf.pow (2, 62)     (* the tagged/boxed boundary region *)

fun genSmall () : IntInf.int = (rndSign ()) * (rndMod 101)        (* -100..100 *)

fun genBoundary () : IntInf.int =
  let val delta = (rndMod 201) - 100                              (* -100..100 *)
  in (rndSign ()) * (twoPow62 + delta) end

fun genBig () : IntInf.int =
  let val e = 80 + (IntInf.toInt (rndMod 221))                    (* exp 80..300 *)
      val mag = IntInf.pow (2, e) + (rndMod (IntInf.pow (2, 40))) (* + low noise *)
  in (rndSign ()) * mag end

(* pick an operand whose class is chosen by `c` (0,1,2). *)
fun genClass 0 = genSmall ()
  | genClass 1 = genBoundary ()
  | genClass _ = genBig ()

(* a nonzero divisor of a chosen class, with a random (incl. negative) sign. *)
fun genDivisor c =
  let val v = genClass c
  in if v = 0 then (if c = 0 then (rndSign ()) * (1 + rndMod 100) else v + 1) else v end

(* ------------------------------------------------------------- emit helpers --- *)
fun emit (label, value) = print ("@@" ^ label ^ "=" ^ value ^ "\n")

(* stringify an IntInf result, catching the exceptions these ops can raise so an
   exception becomes a comparable VALUE (both raise => agree). *)
fun sI (th : unit -> IntInf.int) : string =
  (IntInf.toString (th ())) handle Div => "DIV"
                                 | Overflow => "OVF"
                                 | Domain => "DOM"
                                 | _ => "EXN"
fun sB (th : unit -> bool) : string =
  (Bool.toString (th ())) handle _ => "EXN"

(* ------------------------------------------------------------ the fuzz loop --- *)
(* For each iteration: pick two operand classes (driven by the PRNG), generate a
   pair, and run every operator on it in BOTH inline and ref-forced forms.
   Note: a and b are bound ONCE per iteration so inline and rts forms see the SAME
   operands; classes are chosen by the PRNG so the magnitude mix is randomized but
   deterministic. *)

(* 19 op-pairs per iter * 2 forms = 38 cases/iter; 8 iters = 304 cases + DONE.
   Each iter randomizes both operand classes via the PRNG.  With seed 0w1 the 8
   iterations cover all three magnitude classes (small/boundary/big) in both
   operand positions — incl. big-vs-big (iter 7) and big-as-first-operand
   (iters 7,9-style draws) — and all sign combinations on a, b, and the divisor. *)
val nIters = 8

fun classOf () = IntInf.toInt (rndMod 3)   (* 0,1,2 *)

fun istr i = Int.toString i

fun doIter i =
  let
    val ca = classOf ()
    val cb = classOf ()
    val a  = genClass ca
    val b  = genClass cb
    (* nonzero divisor for the division family: reuse b's class but force nonzero. *)
    val d  = genDivisor cb
    val si = istr i
    fun pair (op_name, inlF, rtsF) =
      ( emit (op_name ^ "_inline_" ^ si, inlF ())
      ; emit (op_name ^ "_rts_" ^ si,    rtsF ()) )
  in
    (* additive / multiplicative *)
    pair ("add", fn () => sI (fn () => a + b),     fn () => sI (fn () => (I a) + (I b)));
    pair ("sub", fn () => sI (fn () => a - b),     fn () => sI (fn () => (I a) - (I b)));
    (* subtraction the OTHER order too — non-commutative, the bug's home turf *)
    pair ("subR", fn () => sI (fn () => b - a),    fn () => sI (fn () => (I b) - (I a)));
    pair ("mul", fn () => sI (fn () => a * b),     fn () => sI (fn () => (I a) * (I b)));
    (* division family — divisor d is guaranteed nonzero (incl. negative). *)
    pair ("div",  fn () => sI (fn () => a div d),  fn () => sI (fn () => (I a) div (I d)));
    pair ("mod",  fn () => sI (fn () => a mod d),  fn () => sI (fn () => (I a) mod (I d)));
    pair ("quot", fn () => sI (fn () => IntInf.quot (a, d)),
                  fn () => sI (fn () => IntInf.quot (I a, I d)));
    pair ("rem",  fn () => sI (fn () => IntInf.rem (a, d)),
                  fn () => sI (fn () => IntInf.rem (I a, I d)));
    (* the other order of div/mod/quot/rem (swap dividend/divisor): use a as the
       divisor when nonzero, else fall back to d to avoid a guaranteed Div on both
       (which would agree but be uninformative). *)
    let val a' = if a = 0 then d else a in
      pair ("divR",  fn () => sI (fn () => b div a'),  fn () => sI (fn () => (I b) div (I a')));
      pair ("remR",  fn () => sI (fn () => IntInf.rem (b, a')),
                     fn () => sI (fn () => IntInf.rem (I b, I a')))
    end;
    (* unary negation and abs *)
    pair ("neg", fn () => sI (fn () => ~ a),       fn () => sI (fn () => ~ (I a)));
    pair ("abs", fn () => sI (fn () => IntInf.abs a),
                 fn () => sI (fn () => IntInf.abs (I a)));
    (* min / max *)
    pair ("min", fn () => sI (fn () => IntInf.min (a, b)),
                 fn () => sI (fn () => IntInf.min (I a, I b)));
    pair ("max", fn () => sI (fn () => IntInf.max (a, b)),
                 fn () => sI (fn () => IntInf.max (I a, I b)));
    (* comparisons — all four *)
    pair ("lt", fn () => sB (fn () => a < b),      fn () => sB (fn () => (I a) < (I b)));
    pair ("le", fn () => sB (fn () => a <= b),     fn () => sB (fn () => (I a) <= (I b)));
    pair ("eq", fn () => sB (fn () => a = b),      fn () => sB (fn () => (I a) = (I b)));
    pair ("gt", fn () => sB (fn () => a > b),      fn () => sB (fn () => (I a) > (I b)));
    (* pow with a small exponent (0..8); base is the chosen a. *)
    let val e = IntInf.toInt (rndMod 9) in
      pair ("pow" , fn () => sI (fn () => IntInf.pow (a, e)),
                    fn () => sI (fn () => IntInf.pow (I a, e)))
    end
  end

val () =
  let
    fun loop i = if i >= nIters then () else (doIter i; loop (i + 1))
  in loop 0 end

val () = print "@@DONE=ok\n"
