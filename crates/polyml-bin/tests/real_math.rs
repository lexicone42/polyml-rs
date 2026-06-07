//! Real (double) math RTS functions on the polyml-rs interpreter.
//!
//! `PolyRealSqrt`/`Sin`/`Cos`/`Floor`/`Ceil`/`Round`/`Trunc`/`Exp`/`Log`/… and the
//! binary `Atan2`/`Pow`/… were previously stubbed to `tagged(0)` — so `Math.sqrt`,
//! `Real.toLargeInt`, etc. silently returned 0, and worse, `Real.toLargeInt` (and
//! the default `Real.floor` under arbitrary-precision int) compute `toArbitrary o
//! realFloor`, where a `tagged(0)` "real" gets its bytes read as a boxed double —
//! wrong value under FixedInt, SEGV under arbitrary-precision int (the Isabelle
//! `time.ML` wall, task #70). Now implemented for real (boxed f64), which fixes
//! Real math AND the SEGV root cause.
//!
//! Pinning this surfaced two further pre-existing bugs in the negative path, both
//! now fixed: (1) `EXTINSTR_WORD_SHIFT_R_ARITH` untagged with a *logical* shift so
//! `Word.~>>` (and thus `IntInf.~>>` for short values) never sign-extended; (2) the
//! `PolyShiftLeft/RightArbitrary` RTS did a logical shift on negatives and returned
//! 0 for boxed bignums. Both go through proper arithmetic (floor) shifts now, so
//! `toArbitrary` of negative and huge reals is correct.
//!
//! `#[ignore]` (needs /tmp/basis_loaded; self-contained):
//! ```sh
//! tools/build-hol4-checkpoints.sh basis
//! cargo test --release -p polyml-bin --test real_math -- --ignored --nocapture
//! ```

mod common;
use common::*;

#[test]
#[ignore = "needs /tmp/basis_loaded (tools/build-hol4-checkpoints.sh basis)"]
fn real_unary_binary_and_tolargeint() {
    let Some(basis) = basis_checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded missing — run tools/build-hol4-checkpoints.sh basis");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun approx (x, y) = Real.abs (x - y) < 1.0E~9;
(* size(CommandLine.name()) is a genuine runtime value the optimizer can't
   constant-fold, so these exercise the real RTS calls (not compile-time folding). *)
val rt = size (CommandLine.name());
fun opR r = r + Real.fromInt rt - Real.fromInt rt;
val () = pr ("SQRT=" ^ Bool.toString (approx (Math.sqrt (opR 2.0), 1.4142135623730951)) ^ "\n");
val () = pr ("SIN=" ^ Bool.toString (approx (Math.sin (opR 0.0), 0.0)) ^ "\n");
val () = pr ("COS=" ^ Bool.toString (approx (Math.cos (opR 0.0), 1.0)) ^ "\n");
val () = pr ("LN=" ^ Bool.toString (approx (Math.ln (Math.exp (opR 1.0)), 1.0)) ^ "\n");
val () = pr ("POW=" ^ Bool.toString (approx (Math.pow (opR 2.0, opR 10.0), 1024.0)) ^ "\n");
val () = pr ("ATAN2=" ^ Bool.toString (approx (Math.atan2 (opR 1.0, opR 1.0), 0.7853981633974483)) ^ "\n");
(* fromLargeInt = PolyFloatArbitraryPrecision (int->real); also IS Real.fromInt
   under arbitrary-precision int, so it must produce a real boxed double — was
   stubbed to tagged(0). *)
val rtL = LargeInt.fromInt rt;
fun opL (i:LargeInt.int) = i + rtL - rtL;
val () = pr ("FLI=" ^ Bool.toString (approx (Real.fromLargeInt (opL 5), 5.0)) ^ "\n");
val () = pr ("FLI_NEG=" ^ Bool.toString (approx (Real.fromLargeInt (opL (~7)), ~7.0)) ^ "\n");
val () = pr ("FLOOR=" ^ Int.toString (Real.floor (opR 3.7)) ^ "\n");
val () = pr ("CEIL=" ^ Int.toString (Real.ceil (opR 3.2)) ^ "\n");
(* the path that was broken (and SEGV'd under arbitrary-int): toLargeInt uses
   toArbitrary o realFloor/Round (the RTS realFloor, not the FixedInt floorFix). *)
val () = pr ("TLI_NEAREST=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST (opR 3.7)) ^ "\n");
val () = pr ("TLI_FLOOR=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEGINF (opR 3.7)) ^ "\n");
(* negatives exercise the arithmetic-right-shift (~>>) sign path in toArbitrary;
   round-half-to-even sends ~2.5 -> ~2. *)
val () = pr ("TLI_NEG=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST (opR (~2.5))) ^ "\n");
val () = pr ("TLI_NEGFLOOR=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEGINF (opR (~3.7))) ^ "\n");
(* huge values go through the boxed-bignum IntInf.<< / ~>> RTS path. *)
val () = pr ("TLI_BIG=" ^ LargeInt.toString (Real.toLargeInt IEEEReal.TO_NEAREST (opR 1152921504606846976.0)) ^ "\n");
pr "REALMATH_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&basis, driver, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(out.contains("REALMATH_DONE"), "driver did not finish.\n{}", tail(&out, 30));
    for f in ["SQRT", "SIN", "COS", "LN", "POW", "ATAN2", "FLI", "FLI_NEG"] {
        assert!(out.contains(&format!("{f}=true")), "{f} math wrong (stubbed?).\n{}", tail(&out, 30));
    }
    assert!(out.contains("FLOOR=3"), "Real.floor wrong.\n{}", tail(&out, 30));
    assert!(out.contains("CEIL=4"), "Real.ceil wrong.\n{}", tail(&out, 30));
    // the formerly-zero / SEGV-under-arbitrary-int path, now correct for normal values
    assert!(out.contains("TLI_NEAREST=4"), "toLargeInt TO_NEAREST 3.7 wrong (was 0).\n{}", tail(&out, 30));
    assert!(out.contains("TLI_FLOOR=3"), "toLargeInt TO_NEGINF 3.7 wrong.\n{}", tail(&out, 30));
    // negatives: round-half-to-even ~2.5 -> ~2; floor ~3.7 -> ~4. These exercise
    // the arithmetic-right-shift sign path that used to give a huge positive.
    assert!(out.contains("TLI_NEG=~2"), "toLargeInt round-to-even of ~2.5 wrong.\n{}", tail(&out, 30));
    assert!(out.contains("TLI_NEGFLOOR=~4"), "toLargeInt TO_NEGINF ~3.7 wrong.\n{}", tail(&out, 30));
    // huge value via the boxed-bignum IntInf shift path
    assert!(out.contains("TLI_BIG=1152921504606846976"), "toLargeInt of 2^60 wrong.\n{}", tail(&out, 30));
}
