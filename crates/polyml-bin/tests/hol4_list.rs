//! HOL4 list structural induction (APPEND laws) on the polyml-rs interpreter.
//!
//! `#[ignore]` (needs /tmp/hol4_num):
//! ```sh
//! tools/build-hol4-checkpoints.sh num
//! cargo test --release -p polyml-bin --test hol4_list -- --ignored --nocapture
//! ```
//!
//! HONEST SCOPE: the proofs `|- !l. APPEND l NIL = l` and
//! `|- !l1 l2 l3. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)` are
//! GENUINE structural list induction (LIST_INDUCT_TAC = HO_MATCH_MP_TAC over the
//! list induction principle; APPEND is *defined* from the list recursion theorem
//! via new_specification). HOWEVER the list *type* and its two principles
//! (`list_INDUCT`, `list_Axiom`) are AXIOMATIZED (`Theory.new_axiom`, labelled
//! `*_AX` in list_append_axiomatized.sml) — NOT derived from a type construction
//! the way numTheory derives `num`. They are the standard initial-algebra axioms
//! for lists (consistent — lists exist), and the general HOL4 `Datatype` package
//! that would derive them is blocked on the SAT subsystem (external minisat) on
//! our runtime. The fully-derived route is proven-viable (pair_tydef_milestone.sml
//! shows new_type_definition works for parametric types here) but is a volume
//! effort. This test asserts both trophies AND that the principles are axioms,
//! so the caveat is part of the contract.

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_num (tools/build-hol4-checkpoints.sh num)"]
fn append_laws_by_list_induction() {
    let Some(num) = num_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_num missing — run tools/build-hol4-checkpoints.sh num");
        return;
    };
    let Some((out, _)) =
        run_support_driver_on(&num, "list_append_axiomatized.sml", 400_000_000_000)
    else {
        eprintln!("SKIP: vendor/hol4 or driver missing");
        return;
    };
    assert!(
        out.contains("LISTAX_DONE"),
        "list driver did not finish.\n{}",
        tail(&out, 40)
    );
    // the two APPEND theorems, proved by genuine structural induction, 0 hyps
    assert!(
        out.contains("APPEND_NIL_HYPS=0"),
        "APPEND l NIL = l had hypotheses.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("APPEND_ASSOC_HYPS=0"),
        "APPEND_ASSOC had hypotheses.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("∀l1 l2 l3. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)"),
        "APPEND_ASSOC not the expected statement.\n{}",
        tail(&out, 40)
    );
    // honesty: the induction principle is an axiom (documented in the contract)
    assert!(
        out.contains("list_INDUCT(AXIOM)_OK"),
        "list_INDUCT should be present and labelled as an axiom.\n{}",
        tail(&out, 40)
    );
    assert!(
        !out.contains("_FAIL"),
        "a list step failed.\n{}",
        tail(&out, 40)
    );
}
