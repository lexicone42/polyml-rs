//! FixedInt / Real-to-int operations raise the SML `Overflow` exception on
//! out-of-range results (and `handle Overflow` catches it) — not silent wrapping.
//!
//! Foundation-audit finding: INSTR_FIXED_ADD/SUB/MULT used wrapping arithmetic and
//! the REAL_TO_INT/FLOAT_TO_INT handlers used a saturating cast, both tagging
//! unconditionally — so `Int.maxInt + 1` returned a wrapped value and `Real.floor`
//! of a huge value a silently-wrong one, instead of raising `Overflow`. The fix
//! raises a packet with `ex_id == TAGGED(5)` (EXC_overflow) so `handle Overflow`
//! matches. This pins that the exception IDENTITY is right (a `handle _` would pass
//! even with a wrong packet; `handle Overflow` only matches TAGGED(5)).
//!
//! `#[ignore]` (needs /tmp/basis_loaded: tools/build-hol4-checkpoints.sh basis):
//! ```sh
//! cargo test --release -p polyml-bin --test overflow -- --ignored --nocapture
//! ```

mod common;
use common::*;

#[test]
#[ignore = "needs /tmp/basis_loaded (tools/build-hol4-checkpoints.sh basis)"]
fn fixed_and_real_ops_raise_overflow() {
    let Some(basis) = basis_checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded missing");
        return;
    };
    // size(CommandLine.name()) is a runtime value the optimizer can't fold, so these
    // exercise the real opcodes (not compile-time constant folding).
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val n = size (CommandLine.name());
fun opI (i:int) = i + n - n;
val () = pr ("ADD=" ^ ((opI (valOf Int.maxInt) + 1; "NO") handle Overflow => "CAUGHT" | _ => "OTHER") ^ "\n");
val () = pr ("SUB=" ^ ((opI (valOf Int.minInt) - 1; "NO") handle Overflow => "CAUGHT" | _ => "OTHER") ^ "\n");
val () = pr ("MULT=" ^ ((opI (valOf Int.maxInt) * 2; "NO") handle Overflow => "CAUGHT" | _ => "OTHER") ^ "\n");
val () = pr ("FLOOR=" ^ ((Real.floor (1.0e30 + Real.fromInt n - Real.fromInt n); "NO") handle Overflow => "CAUGHT" | _ => "OTHER") ^ "\n");
(* normal in-range arithmetic must be UNAFFECTED *)
val () = pr ("NORM_ADD=" ^ Int.toString (opI 40 + 2) ^ "\n");
val () = pr ("NORM_FLOOR=" ^ Int.toString (Real.floor (3.7 + Real.fromInt n - Real.fromInt n)) ^ "\n");
pr "OVF_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&basis, driver, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(out.contains("OVF_DONE"), "driver did not finish.\n{}", tail(&out, 30));
    for op in ["ADD", "SUB", "MULT", "FLOOR"] {
        assert!(
            out.contains(&format!("{op}=CAUGHT")),
            "{op} did not raise an Overflow that `handle Overflow` caught (wrong packet identity?).\n{}",
            tail(&out, 30)
        );
    }
    assert!(out.contains("NORM_ADD=42"), "in-range add changed.\n{}", tail(&out, 30));
    assert!(out.contains("NORM_FLOOR=3"), "in-range floor changed.\n{}", tail(&out, 30));
}
