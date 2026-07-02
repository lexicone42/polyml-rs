#!/usr/bin/env bash
# polyml-rs regression fence — one command to exercise the runtime + headline workloads.
#
#   tools/regression.sh fast   (default) — build + all ALWAYS-ON tests (~2 min):
#       polyml-runtime + polyml-jit lib unit tests, the non-#[ignore] integration
#       tests (cli_run simple bootstrap, golden_sml), and the JIT interp-vs-JIT
#       differential/coverage tests. No /tmp checkpoints needed. Run this before
#       every change.
#   tools/regression.sh full   — fast + build the HOL4/Isabelle checkpoints if
#       missing, then run all #[ignore] integration tests (the headline workloads:
#       MESON/METIS/Pelletier, the Isabelle term + theorem kernels, the int-flip
#       basis, etc.). ~50 min. Run before a release / after a risky runtime change.
#
# Why this exists: the headline capabilities are pinned by #[ignore] tests that
# need manually-built /tmp checkpoints, which GitHub CI cannot build — CI covers
# build/lints/unit + data-free tests only (.github/workflows/ci.yml). This script
# is the practical FULL gate (methodology: docs/correctness-and-safety.md).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
MODE="${1:-fast}"
fail=0
run() { echo; echo ">>> $*"; "$@" || { echo "!!! FAILED: $*"; fail=1; }; }

# Pick a working Python for the deref lint. Plain `python3` is right in CI and
# most environments; some dev setups shim `python3` to a wrapper that only runs
# under `uv run` (it refuses a direct call). Prefer the bare interpreter, fall
# back to `uv run python3` only when the bare one can't execute a trivial
# script — so a REAL lint failure is never masked.
PY="python3"
if ! python3 -c 'pass' >/dev/null 2>&1 && command -v uv >/dev/null 2>&1; then
  PY="uv run python3"
fi

echo "=== polyml-rs regression ($MODE) ==="
run cargo build --release -p polyml-bin -p polyml-jit

echo; echo "--- always-on unit + integration tests ---"
run cargo test --release -p polyml-runtime --lib
# ALL runtime integration targets (tests/*.rs — `--lib` skips them): the export
# round-trip + adversarial fuzz, the tiny-heap GC use-after-free fence (#109),
# the real-threads GC-handshake soundness controls, and the loader-OOB repros.
# Each is cheap (~1 s) and data-free or self-skipping without vendor.
run cargo test --release -p polyml-runtime --tests
run cargo test --release -p polyml-jit
# polyml-image incl. the bicimage reader-robustness fuzz (read_bic totality on
# ~14K real-image mutants + synthetic hostile inputs; the real-image arm skips
# without vendor, the synthetic arm always runs).
run cargo test --release -p polyml-image
run cargo test --release -p polyml-bin            # non-#[ignore]: cli_run, golden_sml, untrusted corpus
# --untrusted deref-surface completeness lint (also a CI step): any new
# image-controlled-operand deref not behind the untrusted gate fails here.
run $PY tools/lint-image-deref.py

if [ "$MODE" = "full" ]; then
  echo; echo "--- building checkpoints (if missing) ---"
  [ -f /tmp/basis_loaded ]  || run tools/build-hol4-checkpoints.sh basis
  [ -f /tmp/hol4_metis ]    || run tools/build-hol4-checkpoints.sh all
  # the datatype chain (num→…→defn→numpair→ind_type→datatype) chains its own
  # prerequisites; expensive, so only built when absent (it persists via
  # tools/persist-ckpts.sh on the dev box).
  [ -f /tmp/hol4_datatype ] || run tools/build-hol4-checkpoints.sh datatype
  [ -f /tmp/arbint_image ]  || run tools/intflip-bootstrap.sh
  # Lagrange-four-square base checkpoint — without it four_square_full_theorem
  # silently self-skips and the flagship theorem goes UNVERIFIED on a green run.
  [ -f /tmp/l4_foursq_star ] || run tools/build-l4-checkpoint.sh
  run tools/isabelle-pure-probe.sh >/dev/null   # applies isabelle patches idempotently
  # warm Isabelle/Pure checkpoint (load the 261 logical-Pure files + export);
  # needed by isabelle_proving. Built when absent (persists on the dev box).
  [ -f /tmp/isabelle_pure ] || run tools/build-isabelle-pure.sh

  echo; echo "--- headline #[ignore] integration suite ---"
  # NB: isabelle_bertrand (~224B steps / 12 GB heap, tens of minutes) and
  # isabelle_quadratic_reciprocity (heavy; reads the committed qr_resume
  # pieces) are the two most expensive Isabelle workloads.
  # Both now carry the shared SOUND_AUDIT_OK certification (oracle-free + axiom
  # allowlist, classical == 1). They dominate the full-tier wall clock.
  ipass=0; ifail=0; iskip=0
  for t in export_roundtrip_live real_math parsetree_introspect overflow isabelle_pure isabelle_pure_arbint \
           isabelle_gauss concurrency_mutex_demo concurrency_sockets \
           concurrency_preempt concurrency_interrupt concurrency_stdin_park \
           concurrency_exit \
           isabelle_kernel isabelle_theorem_kernel isabelle_proving isabelle_sound_audit_negative isabelle_object_logic isabelle_arithmetic isabelle_number_theory isabelle_summation isabelle_ordering isabelle_divisibility isabelle_primes isabelle_classical_primes isabelle_euclid isabelle_primes_3mod4 isabelle_primes_1mod4 isabelle_sqrt2 isabelle_list_theory isabelle_fta isabelle_division isabelle_euclid_lemma isabelle_euclid_list isabelle_fta_unique isabelle_modular isabelle_power isabelle_ntbase isabelle_binom isabelle_sum isabelle_binom_thm isabelle_flt isabelle_gcd isabelle_crt isabelle_combinatorics isabelle_summation_forms isabelle_prodf isabelle_mult_group isabelle_central_binomial isabelle_wilson_pairing isabelle_wilson_inverse isabelle_wilson isabelle_wilson_converse isabelle_wilson_iff isabelle_neg1_qr isabelle_thue isabelle_twosquare isabelle_euler_foundations isabelle_euler isabelle_euler_criterion isabelle_zeckendorf isabelle_four_square isabelle_pyth isabelle_fibonacci isabelle_sigma isabelle_euclid_perfect isabelle_euclid_euler isabelle_twosquare_full isabelle_bertrand isabelle_quadratic_reciprocity intflip_basis \
           hol4_taut hol4_meson hol4_metis hol4_pelletier hol4_num_prover \
           hol4_arith hol4_order hol4_induction hol4_list hol4_simp hol4_fancy \
           hol4_prim_rec hol4_summation \
           hol4_numsimps hol4_pair hol4_defn hol4_datatype \
           hol4_rewrite hol4_tactic hol4_parse hol4_theory hol4_theories hol4_recon; do
    r=$(cargo test --release -p polyml-bin --test "$t" -- --ignored 2>&1 \
        | grep -oE "[0-9]+ passed; [0-9]+ failed" | head -1)
    p=$(echo "$r" | grep -oE "^[0-9]+"); f=$(echo "$r" | grep -oE "[0-9]+ failed" | grep -oE "^[0-9]+")
    ipass=$((ipass + ${p:-0})); ifail=$((ifail + ${f:-0}))
    printf "  %-26s %s\n" "$t" "${r:-NO RESULT}"
    [ "${f:-0}" != "0" ] && fail=1
    [ -z "$r" ] && { iskip=$((iskip+1)); echo "    (NO RESULT — missing checkpoint/vendor; this target is NOT verified)"; }
  done
  echo "  headline integration: $ipass passed, $ifail failed, $iskip target(s) with no result"
  if [ "$iskip" != "0" ]; then
    echo "  !!! $iskip headline target(s) produced NO RESULT — a green run does NOT cover them."
    echo "  !!! (Set REGRESSION_STRICT=1 to make that a failure.)"
    [ "${REGRESSION_STRICT:-0}" = "1" ] && fail=1
  fi

  echo; echo "--- differential vs upstream PolyML (if oracle built) ---"
  if [ -x /tmp/polybuild/poly ] && [ -f /tmp/basis_loaded ]; then
    # The only known divergences are the basis-compiled IntInf.andb/orb stage-0
    # compiler bug (intinf.sml + intinf_bitwise_order.sml, the same andb(~1,2^80)
    # family — a latent UPSTREAM bug we reproduce byte-for-byte; see
    # docs/correctness-and-safety.md). Everything else AGREES.
    # Includes the generative fuzz_{int,word,real,intinf,convert} (numerics) +
    # fuzz_{list,string,array,vector} (structures, ~53.7K cases) per-op drivers,
    # PLUS the whole-program fuzzer's frozen regression subset (genprog/, 300
    # type-directed programs across 5 dimensions — arith_control / lists_hof /
    # datatypes_rec_exn / strings_closures / gc_pressure; see
    # tools/diff-corpus-gen/README.md for how to regenerate/expand).
    tools/diff-oracle.sh --dir tools/diff-corpus || \
      echo "  (differential reported divergences — expected: 2 intinf andb/orb stage-0, else investigate)"
  else
    echo "  (skipped — build the oracle: tools/build-oracle.sh)"
  fi
fi

echo
if [ "$fail" = "0" ]; then echo "=== REGRESSION OK ($MODE) ==="; else echo "=== REGRESSION FAILED ($MODE) ==="; fi
exit $fail
