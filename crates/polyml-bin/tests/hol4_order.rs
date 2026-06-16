//! HOL4 ordering library — the `<=` (LE) laws proved by induction on the
//! polyml-rs interpreter, persisted in `structure numOrder` on /tmp/hol4_order.
//!
//! `#[ignore]` (needs the chain → order):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh order     # …-> num -> order
//! cargo test --release -p polyml-bin --test hol4_order -- --ignored --nocapture
//! ```
//!
//! `LE m n <=> ?p. n = m + p` (a `new_definition`), with reflexivity, zero,
//! `LE m (m+n)`, transitivity, the SUC step, and antisymmetry all proved by
//! induction / the addition laws — no bool_ss / SAT.

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_order (tools/build-hol4-checkpoints.sh order)"]
fn ordering_library_present() {
    let Some(image) = order_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_order missing — run tools/build-hol4-checkpoints.sh order");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun show tag th = pr (tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
val () = show "LE_REFL"    numOrder.LE_REFL;
val () = show "LE_TRANS"   numOrder.LE_TRANS;
val () = show "LE_ANTISYM" numOrder.LE_ANTISYM;
val () = show "SUC_LE"     numOrder.SUC_LE;
val () = show "LE_ADD"     numOrder.LE_ADD;
val clean = List.all (fn th => null (Thm.hyp th))
  [numOrder.LE_REFL, numOrder.ZERO_LE, numOrder.LE_ADD, numOrder.LE_TRANS,
   numOrder.SUC_LE, numOrder.LE_ANTISYM];
val () = pr ("ALL_CLEAN=" ^ Bool.toString clean ^ "\n");
pr "ORDER_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("ORDER_TEST_DONE"),
        "order driver did not finish.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("ALL_CLEAN=true"),
        "an ordering law has hypotheses.\n{}",
        tail(&out, 40)
    );
    for (tag, stmt) in [
        ("LE_TRANS", "∀m n p. LE m n ∧ LE n p ⇒ LE m p"),
        ("LE_ANTISYM", "∀m n. LE m n ∧ LE n m ⇒ m = n"),
        ("SUC_LE", "∀m n. LE (SUC m) (SUC n) ⇔ LE m n"),
    ] {
        assert!(
            out.contains(stmt),
            "{tag} not the expected statement `{stmt}`.\n{}",
            tail(&out, 40)
        );
    }
    assert!(
        !out.contains("_FAIL") && !out.contains("not been declared"),
        "an ordering theorem was unreachable.\n{}",
        tail(&out, 40)
    );
}
