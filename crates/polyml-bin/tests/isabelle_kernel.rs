//! Isabelle's term/type KERNEL runs on the polyml-rs interpreter.
//!
//! `Pure/term.ML` (the Isabelle kernel: the `typ` and `term` datatypes + the core
//! operations — `type_of`, `fastype_of`, `betapply`, `aconv`, `abstract_over`, …)
//! loads on the arbitrary-precision-int image and we construct + manipulate real
//! Isabelle terms with it: λ-abstraction, β-reduction, α-equivalence, the K
//! combinator, and type computation of `Const` applications. This is the Isabelle
//! analogue of the HOL4 kernel milestone.
//!
//! How we get there (all on /tmp/arbint_image, the self-bootstrapped arbitrary-int
//! image): load ROOT0+ROOT Phase 0 (first 27 files) via raw `PolyML.use` to bring up
//! `ml_compiler0`, then files up to `term.ML` via Isabelle's own `ML_file`, which
//! expands `\<^here>` and other bootstrap antiquotations (ml_input). `term.ML` sits
//! at #83, before the Syntax/Context walls — so the kernel loads cleanly at the
//! current 124/282 Pure-load depth.
//!
//! `#[ignore]` (needs /tmp/arbint_image from tools/intflip-bootstrap.sh +
//! vendored Isabelle/Pure):
//! ```sh
//! tools/intflip-bootstrap.sh
//! cargo test --release -p polyml-bin --test isabelle_kernel -- --ignored --nocapture
//! ```

mod common;
use common::*;

use std::path::PathBuf;

fn arbint_image() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/arbint_image");
    p.exists().then_some(p)
}

/// Ordered ML_file paths from ROOT0.ML then ROOT.ML.
fn pure_ml_files(pure: &std::path::Path) -> Vec<String> {
    let mut out = Vec::new();
    for root in ["ROOT0.ML", "ROOT.ML"] {
        let Ok(text) = std::fs::read_to_string(pure.join(root)) else {
            continue;
        };
        for line in text.lines() {
            if let Some(rest) = line.trim().strip_prefix("ML_file ") {
                if let Some(start) = rest.find('"') {
                    if let Some(end) = rest[start + 1..].find('"') {
                        out.push(rest[start + 1..start + 1 + end].to_string());
                    }
                }
            }
        }
    }
    out
}

#[test]
#[ignore = "needs /tmp/arbint_image (tools/intflip-bootstrap.sh) + vendor/isabelle"]
fn term_kernel_constructs_and_reduces() {
    let (Some(pure), Some(image)) = (isabelle_pure_dir(), arbint_image()) else {
        eprintln!("SKIP: /tmp/arbint_image or vendor/isabelle/src/Pure missing");
        return;
    };
    let files = pure_ml_files(&pure);
    // term.ML is #83 in the load order; load up to and including it.
    let upto = files
        .iter()
        .position(|f| f == "term.ML")
        .map_or(files.len(), |i| i + 1);
    let p = pure.to_str().unwrap();
    let quote = |f: &str| format!("\"{p}/{f}\"");
    let ph0_list = files[..27.min(files.len())]
        .iter()
        .map(|f| quote(f))
        .collect::<Vec<_>>()
        .join(",");
    let mid_list = files[27..upto]
        .iter()
        .map(|f| quote(f))
        .collect::<Vec<_>>()
        .join(",");

    let driver = format!(
        r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun qP f = (PolyML.use f) handle _ => ();
val () = List.app qP [{ph0_list}];
fun qM f = (ML_file f) handle _ => ();
val () = List.app qM [{mid_list}];
pr "=KDEMO= start\n";
val natT = Type ("Nat.nat", []);
val idf = Abs ("x", natT, Bound 0);                       (* lam x::nat. x *)
val () = pr ("=KDEMO= fastype_lam " ^ Bool.toString (fastype_of idf = Type("fun",[natT,natT])) ^ "\n");
val () = pr ("=KDEMO= beta " ^ Bool.toString (betapply (idf, Free ("y", natT)) aconv Free ("y", natT)) ^ "\n");
val () = pr ("=KDEMO= alpha " ^ Bool.toString ((Abs ("x", natT, Bound 0)) aconv (Abs ("zzz", natT, Bound 0))) ^ "\n");
val Kc = Abs ("x", natT, Abs ("y", natT, Bound 1));        (* lam x y. x *)
val Kab = betapplys (Kc, [Free ("a", natT), Free ("b", natT)]);
val () = pr ("=KDEMO= K " ^ Bool.toString (Kab aconv Free ("a", natT)) ^ "\n");
val () = pr ("=KDEMO= type_of_K " ^ Bool.toString (type_of Kab = natT) ^ "\n");
val plusT = Type("fun",[natT,Type("fun",[natT,natT])]);
val sum = Const("Groups.plus",plusT) $ Free("a",natT) $ Free("b",natT);
val () = pr ("=KDEMO= type_of_sum " ^ Bool.toString (type_of sum = natT) ^ "\n");
pr "=KDEMO= DONE\n";
"#
    );

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        60_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("=KDEMO= DONE"),
        "kernel demo did not finish.\n{}",
        tail(&out, 40)
    );
    for check in [
        "fastype_lam true",
        "beta true",
        "alpha true",
        "K true",
        "type_of_K true",
        "type_of_sum true",
    ] {
        assert!(
            out.contains(&format!("=KDEMO= {check}")),
            "Isabelle kernel op failed: expected `{check}`.\n{}",
            tail(&out, 40)
        );
    }
}
