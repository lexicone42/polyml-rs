//! THUE'S LEMMA in Isabelle/Pure on the polyml-rs interpreter — the pigeonhole
//! gateway to Fermat's two-square theorem.
//!
//!   thue : ⊢ 0 < p ⟹ ∃ s x1 x2 y1 y2.
//!            (s² ≤ p ∧ p < (s+1)²)                       [s = ⌊√p⌋]
//!            ∧ x1≤s ∧ x2≤s ∧ y1≤s ∧ y2≤s
//!            ∧ ¬(x1=x2 ∧ y1=y2)                          [two DISTINCT grid points]
//!            ∧ cong p (x1 + a·y2) (x2 + a·y1)            [the additive collision]
//!
//! i.e. for the given `a` there are two distinct points in the [0..s]² grid whose
//! `i + a·(s−j)` residues collide mod p — the ℕ-friendly (subtraction-free)
//! collision form of Thue's lemma (`X = x1−x2`, `Y = y1−y2` give `X ≡ a·Y mod p`,
//! `|X|,|Y| ≤ s < √p`, not both 0). A 0-hyp theorem; only classical assumption =
//! `ex_middle`.
//!
//! This required NEW machinery the tower lacked, all proved by kernel inference:
//! `floor_sqrt` (integer √), a list `list_pigeonhole`, a `[0..m−1]` range list,
//! and the crux **image-collision pigeonhole** (`dup_gridres`) — proved DIRECTLY
//! for the concrete residue recursion (NOT an axiomatized `Free f`, which would be
//! unsound), by the "minus-one-value" induction. Then the grid bridge
//! (`rearrange2`, the decode lemmas, `cong_of_rmod`) packages the existential.
//!
//! Built on `common::with_wilson_pairing` (`cong` + the `natlist` list lib,
//! without the heavy Wilson theorem Thue doesn't need) by two ultracode fleets
//! (wf_010172c9-d24 built the infra+bridge + `collision_exists`; wf_67a27224-97d
//! closed the image-collision pigeonhole + packaged Thue — all 3 seats, two
//! routes). Re-verified end-to-end by hand (byte-identical re-derivation,
//! Tagged(0), 55-axiom audit clean, aconv + 0-hyp + distinctness/non-degeneracy
//! soundness probes).
//!
//! NEXT (the dream): Fermat's two-square — instantiate Thue at an `a` with
//! a²≡−1 (we banked −1-is-a-QR for p≡1 mod4), giving u²+v² ≡ 0 mod p with
//! 0 < u²+v² < 2p, hence p = u²+v². Reachable on `with_wilson` (which extends
//! this base with Wilson's theorem) + the banked `isabelle_neg1_qr`.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_thue -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn thues_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_thue.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_thue.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_wilson_pairing(&driver),
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The image-collision pigeonhole (the crux) and the full Thue lemma.
    assert!(
        out.contains("IMGPIGEON_OK"),
        "image-collision pigeonhole did not prove:\n{out}"
    );
    assert!(
        out.contains("THUE_OK"),
        "Thue's lemma did not prove:\n{out}"
    );
    assert!(
        out.contains("THUE_ALL_OK"),
        "THUE_ALL_OK marker missing:\n{out}"
    );
    // Not a degenerate / failed / exceptional run.
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}
