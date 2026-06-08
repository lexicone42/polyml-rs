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
# Why this exists: the headline capabilities are pinned only by #[ignore] tests that
# need manually-built /tmp checkpoints, and there is no CI. This script is the
# practical gate (foundation audit, docs/foundation-audit-2026-06-08.md).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
MODE="${1:-fast}"
fail=0
run() { echo; echo ">>> $*"; "$@" || { echo "!!! FAILED: $*"; fail=1; }; }

echo "=== polyml-rs regression ($MODE) ==="
run cargo build --release -p polyml-bin -p polyml-jit

echo; echo "--- always-on unit + integration tests ---"
run cargo test --release -p polyml-runtime --lib
run cargo test --release -p polyml-jit
run cargo test --release -p polyml-bin            # non-#[ignore]: cli_run, golden_sml

if [ "$MODE" = "full" ]; then
  echo; echo "--- building checkpoints (if missing) ---"
  [ -f /tmp/basis_loaded ]  || run tools/build-hol4-checkpoints.sh basis
  [ -f /tmp/hol4_metis ]    || run tools/build-hol4-checkpoints.sh all
  [ -f /tmp/arbint_image ]  || run tools/intflip-bootstrap.sh
  run tools/isabelle-pure-probe.sh >/dev/null   # applies isabelle patches idempotently

  echo; echo "--- headline #[ignore] integration suite ---"
  ipass=0; ifail=0
  for t in real_math parsetree_introspect isabelle_pure isabelle_pure_arbint \
           isabelle_kernel isabelle_theorem_kernel intflip_basis \
           hol4_taut hol4_meson hol4_metis hol4_pelletier hol4_num_prover \
           hol4_arith hol4_order hol4_induction hol4_list hol4_simp hol4_fancy \
           hol4_rewrite hol4_tactic hol4_parse hol4_theory hol4_theories hol4_recon; do
    r=$(cargo test --release -p polyml-bin --test "$t" -- --ignored 2>&1 \
        | grep -oE "[0-9]+ passed; [0-9]+ failed" | head -1)
    p=$(echo "$r" | grep -oE "^[0-9]+"); f=$(echo "$r" | grep -oE "[0-9]+ failed" | grep -oE "^[0-9]+")
    ipass=$((ipass + ${p:-0})); ifail=$((ifail + ${f:-0}))
    printf "  %-26s %s\n" "$t" "${r:-NO RESULT}"
    [ "${f:-0}" != "0" ] && fail=1
    [ -z "$r" ] && { echo "    (no result — likely skipped: missing checkpoint/vendor)"; }
  done
  echo "  headline integration: $ipass passed, $ifail failed"
fi

echo
if [ "$fail" = "0" ]; then echo "=== REGRESSION OK ($MODE) ==="; else echo "=== REGRESSION FAILED ($MODE) ==="; fi
exit $fail
