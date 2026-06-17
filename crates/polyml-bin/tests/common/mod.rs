//! Shared helpers for the SML / HOL4 reconstruction integration tests.
//!
//! `hol4_recon.rs` predates this module and keeps its own inline copies of
//! the path/run helpers; new test files should `mod common;` and use these.
//! Included via `mod common;` (a subdir module, so Cargo does not compile it
//! as its own test binary).
#![allow(dead_code)]

use std::path::PathBuf;
use std::process::{Command, Stdio};

/// Walk up from this crate's manifest dir to the workspace root.
pub fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let cargo = p.join("Cargo.toml");
        if cargo.exists()
            && std::fs::read_to_string(&cargo)
                .map(|t| t.contains("[workspace]"))
                .unwrap_or(false)
        {
            return p;
        }
        assert!(p.pop(), "could not find workspace root");
    }
}

pub fn poly_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

pub fn vendor_polyml_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml");
    p.exists().then_some(p)
}

pub fn hol4_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/hol4");
    p.exists().then_some(p)
}

/// Vendored Isabelle/Pure ML sources (sparse blobless clone of
/// `github.com/isabelle-prover/mirror-isabelle`, `src/Pure` only). Git-ignored
/// like `vendor/hol4`; obtain with:
///   git clone --filter=blob:none --no-checkout <mirror> vendor/isabelle/mirror-isabelle
///   (cd vendor/isabelle/mirror-isabelle && git sparse-checkout set src/Pure && git checkout)
pub fn isabelle_pure_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/isabelle/mirror-isabelle/src/Pure");
    p.exists().then_some(p)
}

/// The shared classical number-theory foundation driver
/// (`isabelle_support/isabelle_nt_helpers.sml`): object logic + Peano
/// arithmetic + the commutative semiring + the existential quantifier +
/// linear order + divisibility + classical FOL (excluded middle) + the
/// genuine "every n >= 2 has a prime divisor" theorem. Every number-theory
/// driver above the classical layer used to embed this ~3229-line block
/// verbatim; now they carry only their proof-specific delta and the harness
/// splices the foundation in front at run time (see [`with_nt_helpers`]).
pub fn nt_helpers_path() -> PathBuf {
    workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_nt_helpers.sml")
}

/// Prepend the shared classical NT foundation to a driver `delta`, yielding
/// the full source to pipe into `poly run /tmp/isabelle_pure`.
///
/// The foundation begins with `restore_pure_context ()`, so it must run
/// first — exactly what prepending guarantees. The delta files retain their
/// (comment-only) header above the proof; moving it after the foundation is
/// a pure comment reordering, so the executed SML is identical to the old
/// self-contained driver.
pub fn with_nt_helpers(delta: &str) -> String {
    let helpers = std::fs::read_to_string(nt_helpers_path()).expect("read isabelle_nt_helpers.sml");
    format!("{helpers}\n{delta}")
}

/// Prepend Euclid's-theorem development (`isabelle_euclid.sml`: `fact` (n!),
/// `fact_pos`, `dvd_fact`, `consec_coprime`, and the infinitude of primes) on
/// top of the classical foundation, for drivers that build on the factorial /
/// Euclid machinery (e.g. infinitely many primes ≡ 3 mod 4).
pub fn with_euclid(delta: &str) -> String {
    let euclid = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_euclid.sml"),
    )
    .expect("read isabelle_euclid.sml");
    with_nt_helpers(&format!("{euclid}\n{delta}"))
}

/// Prepend the UNIFIED number-theory base to a driver `delta`: the classical
/// foundation (`isabelle_nt_helpers.sml`) PLUS the `isabelle_ntbase.sml`
/// additions — the division theorem (`div_mod_exists`), Euclid, Euclid's lemma,
/// modular congruence (`cong`), and powers. Drivers that need division or
/// modular arithmetic build on this second tier instead of re-embedding it.
pub fn with_ntbase(delta: &str) -> String {
    let ntbase = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_ntbase.sml"),
    )
    .expect("read isabelle_ntbase.sml");
    with_nt_helpers(&format!("{ntbase}\n{delta}"))
}

/// Prepend the full gcd / Bézout development (`isabelle_gcd.sml`: gcd universal
/// property, Bézout's identity, coprime-Bézout, modular inverse) on top of the
/// unified base, for drivers that need modular inverses or Bézout coefficients
/// (e.g. the Chinese Remainder Theorem).
pub fn with_gcd(delta: &str) -> String {
    let gcd = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_gcd.sml"),
    )
    .expect("read isabelle_gcd.sml");
    with_ntbase(&format!("{gcd}\n{delta}"))
}

/// Prepend the binomial-theorem development (`isabelle_binom_thm.sml`: `binom`
/// + Pascal, the higher-order finite sum `sumf` + sum-algebra, `pow`, and the
/// binomial theorem itself) on top of the classical foundation, for drivers
/// that need finite sums / binomial coefficients (e.g. the combinatorial
/// identities). NB this development is self-contained above `with_nt_helpers`
/// (it embeds the `pow`/`sub` pieces it needs), so it builds on the classical
/// foundation directly, not on `with_ntbase`.
pub fn with_binom_thm(delta: &str) -> String {
    let binom_thm = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_binom_thm.sml"),
    )
    .expect("read isabelle_binom_thm.sml");
    with_nt_helpers(&format!("{binom_thm}\n{delta}"))
}

/// Prepend the multiplicative-group-mod-p development (`isabelle_mult_group.sml`:
/// inverse_unique, mod_cancel, lagrange_roots) on top of the gcd / Euclid-lemma
/// base, for drivers that need the Wilson keystones (e.g. the list-product +
/// involution-pairing development toward Wilson's theorem).
pub fn with_mult_group(delta: &str) -> String {
    let mg = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_mult_group.sml"),
    )
    .expect("read isabelle_mult_group.sml");
    with_gcd(&format!("{mg}\n{delta}"))
}

/// Prepend the Wilson-pairing development (`isabelle_wilson_pairing.sml`: the
/// natlist list-product library + the involution `pairing_lemma`) on top of the
/// multiplicative-group base, for the Wilson finale (the residue-range list, the
/// modular-inverse function, and the assembly).
pub fn with_wilson_pairing(delta: &str) -> String {
    let wp = std::fs::read_to_string(
        workspace_root()
            .join("crates/polyml-bin/tests/isabelle_support/isabelle_wilson_pairing.sml"),
    )
    .expect("read isabelle_wilson_pairing.sml");
    with_mult_group(&format!("{wp}\n{delta}"))
}

/// Prepend the Wilson modular-inverse development (`isabelle_wilson_inverse.sml`:
/// rmod/cong_iff_rmod, the residue range `upto`, and the inverse function `finv`)
/// on top of the Wilson-pairing base — the full base for Wilson's theorem itself.
pub fn with_wilson_inverse(delta: &str) -> String {
    let wi = std::fs::read_to_string(
        workspace_root()
            .join("crates/polyml-bin/tests/isabelle_support/isabelle_wilson_inverse.sml"),
    )
    .expect("read isabelle_wilson_inverse.sml");
    with_wilson_pairing(&format!("{wi}\n{delta}"))
}

/// Prepend Wilson's THEOREM (`isabelle_wilson.sml`: `wilson : prime2 p ⟹
/// (p−1)! ≡ −1 (mod p)`) on top of the Wilson modular-inverse base, for drivers
/// that use Wilson's theorem itself (e.g. −1 is a QR mod p for p ≡ 1 mod 4 via
/// the `((p−1)/2)!` construction).
pub fn with_wilson(delta: &str) -> String {
    let w = std::fs::read_to_string(
        workspace_root().join("crates/polyml-bin/tests/isabelle_support/isabelle_wilson.sml"),
    )
    .expect("read isabelle_wilson.sml");
    with_wilson_inverse(&format!("{w}\n{delta}"))
}

/// Prepend the combinatorial-identities development (`isabelle_combinatorics.sml`:
/// Pascal row sum, hockey stick, and Vandermonde) on top of the binomial-theorem
/// base, for drivers that build on those identities (e.g. the central binomial
/// coefficient identity, a Vandermonde corollary).
pub fn with_combinatorics(delta: &str) -> String {
    let comb = std::fs::read_to_string(
        workspace_root()
            .join("crates/polyml-bin/tests/isabelle_support/isabelle_combinatorics.sml"),
    )
    .expect("read isabelle_combinatorics.sml");
    with_binom_thm(&format!("{comb}\n{delta}"))
}

/// Basis-only warm checkpoint (`tools/build-hol4-checkpoints.sh basis`).
pub fn basis_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/basis_loaded");
    p.exists().then_some(p)
}

/// Warm basis+kernel checkpoint built by `tools/build-hol4-checkpoints.sh kernel`.
pub fn kernel_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_kernel");
    p.exists().then_some(p)
}

/// Warm basis+kernel+Theory+parser checkpoint built by
/// `tools/build-hol4-checkpoints.sh parse`.
pub fn parse_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_parse");
    p.exists().then_some(p)
}

/// Warm parser+bool-theory checkpoint built by
/// `tools/build-hol4-checkpoints.sh bool`.
pub fn bool_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_bool");
    p.exists().then_some(p)
}

/// Warm bool+tactic-layer checkpoint built by
/// `tools/build-hol4-checkpoints.sh tactic`.
pub fn tactic_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_tactic");
    p.exists().then_some(p)
}

/// Warm tactic+REWRITE_TAC checkpoint built by
/// `tools/build-hol4-checkpoints.sh rewrite`.
pub fn rewrite_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_rewrite");
    p.exists().then_some(p)
}

/// Warm checkpoint with markerTheory (`tools/build-hol4-checkpoints.sh marker`).
pub fn marker_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_marker");
    p.exists().then_some(p)
}

/// Warm checkpoint with combinTheory (`tools/build-hol4-checkpoints.sh combin`).
pub fn combin_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_combin");
    p.exists().then_some(p)
}

/// Warm checkpoint with simpLib / SIMP_TAC (`tools/build-hol4-checkpoints.sh simp`).
pub fn simp_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_simp");
    p.exists().then_some(p)
}

/// Warm checkpoint with numTheory (`tools/build-hol4-checkpoints.sh num`).
pub fn num_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_num");
    p.exists().then_some(p)
}

/// Warm checkpoint with the arithmetic library `structure numArith`
/// (`tools/build-hol4-checkpoints.sh arith`).
pub fn arith_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_arith");
    p.exists().then_some(p)
}

/// Warm checkpoint with the ordering library `structure numOrder`
/// (`tools/build-hol4-checkpoints.sh order`).
pub fn order_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_order");
    p.exists().then_some(p)
}

/// Warm checkpoint with the REAL prim_recTheory (Datatype roadmap Stage 1:
/// num_Axiom, SIMP_REC/PRIM_REC, the LESS theory)
/// (`tools/build-hol4-checkpoints.sh prim`).
pub fn prim_rec_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_prim_rec");
    p.exists().then_some(p)
}

/// Warm checkpoint with HolSatLib + tautLib (propositional tautology proving
/// via the pure-SML DPLL solver) (`tools/build-hol4-checkpoints.sh taut`).
pub fn taut_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_taut");
    p.exists().then_some(p)
}

/// Warm checkpoint with mesonLib (first-order automated proving, MESON_TAC)
/// (`tools/build-hol4-checkpoints.sh meson`).
pub fn meson_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_meson");
    p.exists().then_some(p)
}

/// Warm checkpoint with metisLib (resolution/paramodulation prover, METIS_TAC)
/// (`tools/build-hol4-checkpoints.sh metis`).
pub fn metis_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_metis");
    p.exists().then_some(p)
}

/// Pipe the contents of a `hol4_support/*.sml` driver into `poly run <image>`
/// (cwd = vendor/polyml), with `HOL4_DIR` set to `vendor/hol4`. Returns None if
/// `image`, the driver, or `vendor/hol4` are absent (caller should skip).
pub fn run_support_driver_on(
    image: &std::path::Path,
    driver_name: &str,
    max_steps: u64,
) -> Option<(String, i32)> {
    let hol = hol4_dir()?;
    let src = std::fs::read_to_string(support_file(driver_name)).ok()?;
    run_image_env(
        image,
        &src,
        max_steps,
        &[("HOL4_DIR", hol.to_str().unwrap())],
    )
}

/// A file under `crates/polyml-bin/tests/hol4_support/`.
pub fn support_file(name: &str) -> PathBuf {
    workspace_root()
        .join("crates/polyml-bin/tests/hol4_support")
        .join(name)
}

/// Pipe `sml` into `poly run <image>` (cwd = vendor/polyml), with extra env.
/// Returns (combined stdout+stderr, exit code), or None if poly can't spawn.
pub fn run_image_env(
    image: &std::path::Path,
    sml: &str,
    max_steps: u64,
    envs: &[(&str, &str)],
) -> Option<(String, i32)> {
    let vendor = vendor_polyml_dir()?;
    let mut cmd = Command::new(poly_bin());
    cmd.current_dir(&vendor)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99")
        .env("POLYML_GC_QUIET", "1");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let mut child = cmd.spawn().ok()?;
    // Write the driver to stdin on a SEPARATE THREAD so the parent can drain
    // stdout/stderr concurrently. Writing all of stdin on this thread *before*
    // reading stdout deadlocks for large drivers: once poly's stdout pipe fills
    // (~64KB) it blocks on write -> stops reading stdin -> our write_all blocks
    // (stdin pipe also full). This bit the big Euclid/FTA-arc drivers (4000+
    // lines of stdin + lots of OK-marker output). wait_with_output() below reads
    // stdout/stderr to EOF while this thread feeds stdin.
    let mut stdin = child.stdin.take().unwrap();
    let sml_bytes = sml.as_bytes().to_vec();
    let writer = std::thread::spawn(move || {
        use std::io::Write;
        let _ = stdin.write_all(&sml_bytes);
        // stdin dropped here -> EOF for the child
    });
    let out = child.wait_with_output().ok()?;
    let _ = writer.join();
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some((combined, out.status.code().unwrap_or(-1)))
}

/// Load the captured Theory-subsystem reconstruction
/// (`hol4_support/theory_subsystem.sml`) on the warm kernel checkpoint, then
/// run `extra_sml`. Returns None if `/tmp/hol4_kernel` or `vendor/hol4` are
/// absent (caller should skip).
pub fn run_theory_subsystem(extra_sml: &str, max_steps: u64) -> Option<(String, i32)> {
    let kernel = kernel_checkpoint_path()?;
    let hol = hol4_dir()?;
    // Pipe the loader's source into the REPL rather than `PolyML.use`-ing it:
    // when the whole file is one `PolyML.use` unit, an uncaught exception
    // (e.g. a "Cannot open") propagates through the use machinery and trips an
    // interpreter exception-unwinding halt; piped, each top-level declaration
    // is handled independently (matches hol4_recon.rs's working tests).
    let loader_src = std::fs::read_to_string(support_file("theory_subsystem.sml")).ok()?;
    let driver = format!("{loader_src}\n{extra_sml}");
    run_image_env(
        &kernel,
        &driver,
        max_steps,
        &[("HOL4_DIR", hol.to_str().unwrap())],
    )
}

// ----------------------------------------------------------------------------
// Compile-output analysis (mirrors tools/sml-exp.sh's grouping on the Rust side)
// ----------------------------------------------------------------------------

/// Parse a `LOADED_OK n/m` marker emitted by the fixpoint loader.
pub fn parse_loaded(out: &str) -> Option<(usize, usize)> {
    for line in out.lines() {
        if let Some(idx) = line.find("LOADED_OK") {
            let rest = &line[idx + "LOADED_OK".len()..];
            let tok = rest.split_whitespace().next()?; // "50/54"
            let (a, b) = tok.split_once('/')?;
            return Some((a.trim().parse().ok()?, b.trim().parse().ok()?));
        }
    }
    None
}

/// Extract `(X)` from a line like `... (Foo) has not been declared`.
fn paren_ident(line: &str) -> Option<&str> {
    let start = line.find('(')? + 1;
    let end = line[start..].find(')')? + start;
    Some(&line[start..end])
}

fn count_distinct<'a>(items: impl Iterator<Item = &'a str>) -> Vec<(String, usize)> {
    let mut map: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for it in items {
        *map.entry(it.to_string()).or_insert(0) += 1;
    }
    let mut v: Vec<_> = map.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    v
}

/// A grouped, human-readable summary of compile diagnostics in `out`, suitable
/// for an assertion-failure message. Empty-ish when there are no errors.
pub fn classify_errors(out: &str) -> String {
    let mut s = String::new();

    if let Some((a, b)) = parse_loaded(out) {
        s.push_str(&format!("modules: {a}/{b} loaded\n"));
        for line in out.lines() {
            if let Some(i) = line.find("STUCKERR ") {
                let f = line[i + "STUCKERR ".len()..].trim();
                let base = f.rsplit('/').next().unwrap_or(f);
                s.push_str(&format!("  stuck: {base}\n"));
            }
        }
    }

    let undeclared_structs = count_distinct(
        out.lines()
            .filter(|l| l.contains("Structure (") && l.contains("has not been declared"))
            .filter_map(paren_ident),
    );
    if !undeclared_structs.is_empty() {
        s.push_str("undeclared structures:\n");
        for (name, n) in undeclared_structs.iter().take(20) {
            s.push_str(&format!("  {n:>3} {name}\n"));
        }
    }

    let undeclared_vals = count_distinct(
        out.lines()
            .filter(|l| {
                (l.contains("Value or constructor (") || l.contains("Constructor ("))
                    && l.contains("has not been declared")
            })
            .filter_map(paren_ident),
    );
    if !undeclared_vals.is_empty() {
        s.push_str("undeclared values/constructors:\n");
        for (name, n) in undeclared_vals.iter().take(20) {
            s.push_str(&format!("  {n:>3} {name}\n"));
        }
    }

    let type_errs = out
        .lines()
        .filter(|l| l.contains("error: Type error"))
        .count();
    if type_errs > 0 {
        s.push_str(&format!("type errors: {type_errs}\n"));
    }
    let sig_mismatch = out
        .lines()
        .filter(|l| l.contains("Structure does not match signature"))
        .count();
    if sig_mismatch > 0 {
        s.push_str(&format!("signature mismatches: {sig_mismatch}\n"));
    }
    let static_errs = out.lines().filter(|l| l.contains("Static Errors")).count();
    if static_errs > 0 {
        s.push_str(&format!("Static Errors lines: {static_errs}\n"));
    }

    if s.is_empty() {
        s.push_str("(no recognized compile diagnostics)\n");
    }
    s
}

/// Last `n` lines of `out`, for compact assertion messages.
pub fn tail(out: &str, n: usize) -> String {
    let lines: Vec<&str> = out.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}
