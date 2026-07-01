//! THE embedding demo: load and run a Poly/ML heap image from a
//! downstream crate in a few lines of SAFE code, via [`Session`].
//! (Every other example in this directory is an adversarial security
//! reproducer, not an API showcase — start here.)
//!
//! Usage:
//! ```text
//! cargo run --release -p polyml-runtime --example embed_run_image -- \
//!     vendor/polyml/bootstrap/bootstrap64.txt
//! ```
//! On the standard bootstrap this reports exactly 1,110,805 steps and
//! `Tagged(0)` — byte-identical to `poly run`.

use polyml_runtime::{RunOutcome, Session, SessionConfig};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: embed_run_image <image>");
    let bytes = std::fs::read(&path).expect("read image");

    let mut session = Session::from_bytes(&bytes, SessionConfig::default()).expect("load image");
    let result = session.run(5_000_000);

    println!("Executed {} bytecode step(s).", result.steps);
    match result.outcome {
        RunOutcome::Returned(v) => println!("Result: {v:?}"),
        other => println!("Result: {other:?}"),
    }
}
