#!/usr/bin/env bash
# diff-threads.sh — the differential oracle pointed at THREADING.
#
# Runs deterministic threaded SML programs (tools/diff-corpus-threads/:
# mutex counting, forced condvar alternation, trylock semantics, timed
# waits, thread-local storage, death-by-uncaught-exception) through real
# upstream Poly/ML (native threads) and through our runtime in BOTH
# threading modes (giant lock, POLY_PARALLEL), comparing the `@@` output
# lines. The corpus is built so output is deterministic REGARDLESS of
# scheduling — any diff is a semantic divergence, not noise.
#
# Env: POLY_UPSTREAM (default /tmp/polybuild/poly)
#      POLY_OURS     (default ./target/release/poly)
#      POLY_CKPT     (default /tmp/basis_loaded)
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
UPSTREAM="${POLY_UPSTREAM:-/tmp/polybuild/poly}"
OURS="${POLY_OURS:-./target/release/poly}"
CKPT="${POLY_CKPT:-/tmp/basis_loaded}"
[ -x "$UPSTREAM" ] || { echo "missing upstream oracle: $UPSTREAM (tools/build-oracle.sh)"; exit 2; }
[ -f "$CKPT" ] || { echo "missing checkpoint: $CKPT"; exit 2; }

extract() { grep -ao '@@[^[:cntrl:]]*' || true; }

total=0; pass=0; diverge=0; divlist=()
for f in tools/diff-corpus-threads/*.sml; do
  total=$((total+1))
  up=$(timeout 90 "$UPSTREAM" < "$f" 2>&1 | extract)
  giant=$(POLY_REAL_THREADS=1 POLYML_GC_QUIET=1 \
      timeout 180 "$OURS" run --max-steps 40000000000 "$CKPT" < "$f" 2>&1 | extract)
  par=$(POLY_REAL_THREADS=1 POLY_PARALLEL=1 POLYML_GC_QUIET=1 \
      timeout 180 "$OURS" run --max-steps 40000000000 "$CKPT" < "$f" 2>&1 | extract)
  if [ -n "$up" ] && [ "$up" = "$giant" ] && [ "$up" = "$par" ]; then
    pass=$((pass+1))
    echo "AGREE $(basename "$f")  ($up)"
  elif [ -z "$up" ]; then
    echo "EMPTY $(basename "$f") — upstream produced no @@ output"
    diverge=$((diverge+1)); divlist+=("$f")
  else
    diverge=$((diverge+1)); divlist+=("$f")
    echo "DIVERGE $(basename "$f")"
    echo "  upstream: $up"
    echo "  giant   : $giant"
    echo "  parallel: $par"
  fi
done
echo
echo "=== diff-threads: $pass/$total agree (both modes), $diverge diverged ==="
[ "$diverge" -eq 0 ]
