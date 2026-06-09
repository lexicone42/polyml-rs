#!/usr/bin/env bash
# diff-oracle.sh — differential correctness test against upstream PolyML.
#
# Runs one or more SML snippets through BOTH the real upstream `poly` (the
# ground-truth oracle) and our Rust `poly run <checkpoint>`, then compares the
# `@@`-tagged result lines. Any difference (beyond cosmetic REPL chatter, which
# the @@ filter strips) is a faithfulness bug in OUR implementation.
#
# Each snippet must print its results as lines of the form:
#     @@<label>=<value>
# e.g.  print ("@@maxint=" ^ Int.toString (valOf Int.maxInt) ^ "\n");
# The harness extracts substrings from `@@` to end-of-line on each side, so the
# REPL prompt prefix ("> ") and banner are ignored automatically.
#
# Usage:
#   tools/diff-oracle.sh <file.sml> [file2.sml ...]
#   tools/diff-oracle.sh --dir <dir-of-.sml>
# Env overrides:
#   POLY_UPSTREAM (default /tmp/polybuild/poly)
#   POLY_OURS     (default ./target/release/poly)
#   POLY_CKPT     (default /tmp/basis_loaded)
#   POLY_MAXSTEPS (default 20000000000)
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
UPSTREAM="${POLY_UPSTREAM:-/tmp/polybuild/poly}"
OURS="${POLY_OURS:-$ROOT/target/release/poly}"
CKPT="${POLY_CKPT:-/tmp/basis_loaded}"
MAXSTEPS="${POLY_MAXSTEPS:-20000000000}"

[ -x "$UPSTREAM" ] || { echo "FATAL: upstream poly not found/executable at $UPSTREAM"; exit 2; }
[ -x "$OURS" ]     || { echo "FATAL: our poly not found at $OURS (cargo build --release -p polyml-bin)"; exit 2; }
[ -f "$CKPT" ]     || { echo "FATAL: checkpoint not found at $CKPT"; exit 2; }

# Collect snippet list.
files=()
if [ "${1:-}" = "--dir" ]; then
  shift
  while IFS= read -r f; do files+=("$f"); done < <(find "$1" -name '*.sml' | sort)
else
  files=("$@")
fi
[ "${#files[@]}" -gt 0 ] || { echo "usage: $0 <file.sml ...> | --dir <dir>"; exit 2; }

extract() { grep -ao '@@[^[:cntrl:]]*' || true; }

total=0; pass=0; diverge=0
divlist=()
for f in "${files[@]}"; do
  total=$((total+1))
  up=$(timeout 90  "$UPSTREAM" < "$f" 2>&1 | extract)
  ours=$(timeout 180 "$OURS" run --max-steps "$MAXSTEPS" "$CKPT" < "$f" 2>&1 | extract)
  if [ "$up" = "$ours" ] && [ -n "$up" ]; then
    pass=$((pass+1))
    # echo "PASS  $(basename "$f")  (${up//$'\n'/ | })"
  elif [ -z "$up" ] && [ -z "$ours" ]; then
    echo "EMPTY $(basename "$f")  — no @@ lines from EITHER side (snippet bug?)"
  else
    diverge=$((diverge+1)); divlist+=("$f")
    echo "DIVERGE $(basename "$f")"
    diff <(printf '%s\n' "$up") <(printf '%s\n' "$ours") \
      | sed -e 's/^</  upstream:/' -e 's/^>/  ours    :/' | grep -E '^  (upstream|ours)' || true
  fi
done

echo
echo "=== diff-oracle: $pass/$total agree, $diverge diverged ==="
if [ "$diverge" -gt 0 ]; then
  printf 'diverged files:\n'; printf '  %s\n' "${divlist[@]}"
  exit 1
fi
