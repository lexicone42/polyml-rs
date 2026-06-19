//! PYTHAGOREAN TRIPLES — the KEY LEMMA and the full CHARACTERIZATION, in
//! Isabelle/Pure on the polyml-rs interpreter.
//!
//!   key_lemma : ⊢ (∀d. d∣u ⟹ d∣v ⟹ d = 1)   (* coprime u v *)
//!               ⟹ u·v = w·w
//!               ⟹ (∃s. u = s·s) ∧ (∃t. v = t·t)
//!
//! "A product of coprime naturals is a perfect square only if each factor is."
//! This is the crux of the characterization of primitive Pythagorean triples
//! (it is applied to the two coprime factors (c−a)/2 and (c+a)/2 whose product
//! is (b/2)²), and an independently valuable, bankable number-theory lemma.
//!
//! ROUTE B (Euclid's lemma + strong induction on w): a prime p∣u divides w·w,
//! hence p∣w (Euclid); p∤v (coprimality + 1<p); p²∣u and cancelling p² (twice,
//! via the locally-proved `mult_left_cancel`) descends to u'·v = w'² with w'<w,
//! coprime u' v, so the IH at w' squares both factors. The u≤1 base cases are
//! direct (u=1 ⟹ v=w² ; u=0 ⟹ w=0 and coprimality forces v=1).
//!
//! Local helper lemmas proved en route (each 0-hyp): `mult_eq_zero`
//! (a·b=0 ⟹ a=0 ∨ b=0), `mult_left_cancel` (0<p ⟹ p·a=p·b ⟹ a=b),
//! `lt_self_mult` (1<c ⟹ 0<n ⟹ n < c·n).
//!
//!   pyth_char (the CHARACTERIZATION, subtraction-free) :
//!     ⊢ pyth_triple(a,b,c) ⟹ primitive(a,b) ⟹ even b ⟹
//!         ∃m n. n<m ∧ coprime(m,n)
//!               ∧ c = m²+n² ∧ b = 2mn ∧ a + n² = m²   (i.e. a = m²−n²)
//!   where pyth_triple(a,b,c) = 0<a ∧ 0<b ∧ a²+b²=c² and
//!   primitive/coprime is the ∀-divisor predicate ∀d. d∣u⟹d∣v⟹d=1.
//!   I.e. every PRIMITIVE Pythagorean triple with the even leg b arises as
//!   (m²−n², 2mn, m²+n²) for some coprime m>n.
//!
//!   The proof, all on with_gcd / ctxtS2 (no new constant, no new axiom):
//!   PARITY machinery built from div_mod_exists at 2 — `parity` (even∨odd),
//!   `even_sq`/`odd_sq` (square parity), `even_odd_absurd` (disjointness via
//!   div_mod_unique), `odd_add_odd_even`.  From these: a is odd and c is odd
//!   (b even + coprime + the squares' parity), c>a with c=a+d (sq monotone +
//!   le_total + a²<c² from b²>0), and b²=d(2a+d) (the (c+a)(c−a) identity in
//!   witnessed form).  Then d is even (=2δ), c+a=2f with f=a+δ, and β²=δf
//!   (cancel 4); δ,f are coprime (a common divisor divides a and β², and a
//!   prime factor would meet primitivity); the KEY LEMMA squares them
//!   (δ=n², f=m²); reassembly gives the five conjuncts (n<m via `lt_sq_rev`,
//!   coprime m n from coprime δ f, c=m²+n², b=2mn via `sqrt_unique`, a+n²=m²).
//!   Two more reusable 0-hyp lemmas en route: `sqrt_unique` (x²=y²⟹x=y) and
//!   `lt_sq_rev` (n²<m²⟹n<m).  ~2.28B steps, Tagged(0).
//!
//! Built on `common::with_gcd` (the classical foundation + division theorem +
//! Euclid + Euclid's lemma + modular cong + powers + the gcd/Bézout development),
//! the lightest banked base carrying coprimality + Euclid's lemma + the semiring.
//! Final context: ctxtS2 / ctermS2 (gcd adds no new context; it works on
//! ntbase's ctxtS2). Both results are validated 0-hyp AND `aconv` their intended
//! schematic goals, plus soundness probes (key: the coprime-dropped variant —
//! false, e.g. 2·2 = 2·2 with 2 not a square — is rejected; char: dropping the
//! even-b or the primitive hypothesis changes the theorem).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_pyth -- --ignored --nocapture
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
fn pythagorean_key_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_pyth.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_pyth.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_gcd(&driver),
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

    // the gcd base must load first (its phase markers)
    assert!(
        out.contains("GCD_PROPS_OK") && out.contains("MOD_INVERSE_OK"),
        "with_gcd base did not load:\n{out}"
    );
    // the key lemma checked (aconv intended, 0-hyp) and its probe held
    assert!(
        out.contains("OK key_lemma"),
        "key_lemma did not check (aconv/0-hyp):\n{out}"
    );
    assert!(
        out.contains("PROBE_OK key needs coprime"),
        "soundness probe (needs coprime) missing:\n{out}"
    );
    assert!(out.contains("KEY_OK"), "marker KEY_OK missing:\n{out}");
    // no kernel failure, no compile error, no soundness probe firing
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors"),
        "static errors during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("KEY_FAILED"), "KEY_FAILED fired:\n{out}");
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn pythagorean_characterization() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_pyth.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_pyth.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_gcd(&driver),
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

    // base + key lemma must load (prereqs for the characterization)
    assert!(
        out.contains("GCD_PROPS_OK") && out.contains("KEY_OK"),
        "base / key lemma did not load:\n{out}"
    );
    // the characterization checked (aconv intended schematic statement, 0-hyp)
    assert!(
        out.contains("OK pyth_char"),
        "pyth_char did not check (aconv/0-hyp):\n{out}"
    );
    // both soundness probes held (dropping even-b or primitive changes the theorem)
    assert!(
        out.contains("PROBE_OK char needs even-b"),
        "soundness probe (needs even-b) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK char needs primitive"),
        "soundness probe (needs primitive) missing:\n{out}"
    );
    assert!(
        out.contains("PYTH_CHAR_OK"),
        "marker PYTH_CHAR_OK missing:\n{out}"
    );
    // no kernel failure, no compile error, no soundness probe firing
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors"),
        "static errors during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(
        !out.contains("PYTH_CHAR_FAILED"),
        "PYTH_CHAR_FAILED fired:\n{out}"
    );
}

/// The GENERATION half (the easy converse): the parametrized form
/// `(m²−n², 2mn, m²+n²)` is always a Pythagorean triple for `n < m`.
/// Stated subtraction-freely (∃d. m²=n²+d ∧ d²+(2mn)²=(m²+n²)²). With the
/// characterization above, this is the full parametrization (both directions).
/// Lives in its own delta (`isabelle_pyth_gen.sml`) — a pure semiring identity.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn pythagorean_generation() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_pyth_gen.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_pyth_gen.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_gcd(&driver),
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

    // the gcd base loaded, the generation identity checked (aconv/0-hyp), probe held
    assert!(
        out.contains("GCD_PROPS_OK"),
        "with_gcd base did not load:\n{out}"
    );
    assert!(
        out.contains("OK generation"),
        "generation identity did not check (aconv/0-hyp):\n{out}"
    );
    assert!(out.contains("GEN_OK"), "marker GEN_OK missing:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors"),
        "static errors during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("GEN_FAILED"), "GEN_FAILED fired:\n{out}");
}
