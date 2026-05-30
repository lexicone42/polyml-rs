#!/usr/bin/env bash
# sml-exp.sh -- run an SML driver against a Poly/ML checkpoint image and
# print ONE structured summary. Designed so a single invocation yields the
# whole picture (handy when terminal output is noisy, batched, or huge):
# the script does all the grepping internally and also writes the summary
# to a sibling .summary file, so the result survives even if stdout is lost.
#
# Usage:
#   tools/sml-exp.sh [options] <checkpoint> <driver.sml>
#
# Options:
#   --steps N     max bytecode steps (default 200000000000)
#   --cwd DIR     working dir for the poly process (default: <repo>/vendor/polyml
#                 if present, else $PWD) -- affects relative file opens
#   --log PATH    full-output log path (default: /tmp/sml-exp-<driver>.log)
#   --tail N      also include the last N raw output lines (default 0)
#   --raw         additionally dump the full raw log to stdout
#   -h|--help     show this header
#
# Env:
#   POLY          path to the poly binary (default: <repo>/target/release/poly)
#
# Recognized driver conventions (all optional -- emit from your SML driver):
#   "LOADED_OK n/m" / "STUCK_COUNT n"   -> module-load tally
#   "STUCKERR <path>"                   -> one per stuck module
#   tokens matching *_OK / *_DONE / *_FAIL / *_PASS -> shown as sentinels
#
# Exit status: the poly process's exit code.
set -uo pipefail

STEPS=200000000000
CWD=""
LOG=""
TAIL=0
RAW=0

while [ $# -gt 0 ]; do
  case "$1" in
    --steps) STEPS="$2"; shift 2;;
    --cwd)   CWD="$2"; shift 2;;
    --log)   LOG="$2"; shift 2;;
    --tail)  TAIL="$2"; shift 2;;
    --raw)   RAW=1; shift;;
    -h|--help) sed -n '2,33p' "$0"; exit 0;;
    --) shift; break;;
    -*) echo "unknown option: $1" >&2; exit 2;;
    *) break;;
  esac
done

CKPT="${1:-}"; DRIVER="${2:-}"
if [ -z "$CKPT" ] || [ -z "$DRIVER" ]; then
  echo "usage: tools/sml-exp.sh [--steps N] [--cwd DIR] <checkpoint> <driver.sml>" >&2
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/.." && pwd)"
POLY="${POLY:-$REPO/target/release/poly}"

[ -x "$POLY" ]   || { echo "poly binary not found/executable: $POLY (set \$POLY)" >&2; exit 2; }
[ -f "$CKPT" ]   || { echo "checkpoint not found: $CKPT" >&2; exit 2; }
[ -f "$DRIVER" ] || { echo "driver not found: $DRIVER" >&2; exit 2; }

if [ -z "$CWD" ]; then
  if [ -d "$REPO/vendor/polyml" ]; then CWD="$REPO/vendor/polyml"; else CWD="$PWD"; fi
fi
if [ -z "$LOG" ]; then
  LOG="/tmp/sml-exp-$(basename "$DRIVER" .sml).log"
fi

# Absolutize checkpoint + driver: the run happens inside `( cd "$CWD" && … )`,
# so relative paths (and the `< "$DRIVER"` redirect) would otherwise resolve
# against $CWD rather than the caller's cwd.
CKPT="$(cd "$(dirname "$CKPT")" && pwd)/$(basename "$CKPT")"
DRIVER="$(cd "$(dirname "$DRIVER")" && pwd)/$(basename "$DRIVER")"

# --- run ---
( cd "$CWD" && "$POLY" run --max-steps "$STEPS" "$CKPT" < "$DRIVER" ) > "$LOG" 2>&1
RC=$?

# --- summarize ---
SUM="${LOG%.log}.summary"
{
  echo "=== sml-exp summary ==="
  echo "driver:     $DRIVER"
  echo "checkpoint: $CKPT"
  echo "cwd:        $CWD"
  echo "exit:       $RC"
  echo "log:        $LOG  ($(wc -l <"$LOG" 2>/dev/null) lines, $(wc -c <"$LOG" 2>/dev/null) bytes)"

  echo
  echo "--- result ---"
  grep -aE "Result:|Executed [0-9]+ bytecode" "$LOG" | tail -3

  if grep -qaE "LOADED_OK|STUCK_COUNT|STUCKERR" "$LOG"; then
    echo
    echo "--- module load (fixpoint markers) ---"
    grep -aE "LOADED_OK|STUCK_COUNT" "$LOG" | tail -2 | sed -E 's/^[ >#]*//'
    if grep -qaE "STUCKERR " "$LOG"; then
      echo "stuck modules:"
      grep -aE "STUCKERR " "$LOG" | sed -E 's#.*STUCKERR +##; s#.*/##' | sort -u | sed 's/^/    /'
    fi
  fi

  sentinels=$(grep -aoE "[A-Z][A-Z0-9_]*(_OK|_DONE|_FAIL|_PASS)" "$LOG" | sort -u | tr '\n' ' ')
  if [ -n "${sentinels// /}" ]; then
    echo
    echo "--- sentinels ---"
    echo "    $sentinels"
  fi

  nerr=$(grep -acE ": error:|poly: .*error|Static Errors|Exception-" "$LOG")
  echo
  echo "--- diagnostics ($nerr error/exception lines) ---"

  us=$(grep -aoE "Structure \([A-Za-z0-9_.]+\) has not been declared" "$LOG" | sed -E 's/.*\(([A-Za-z0-9_.]+)\).*/\1/' | sort | uniq -c | sort -rn)
  [ -n "$us" ] && { echo "undeclared structures:"; echo "$us" | sed 's/^/    /'; }

  uv=$(grep -aoE "(Value or constructor|Constructor) \([A-Za-z0-9_.]+\) has not been declared" "$LOG" | sed -E 's/.*\(([A-Za-z0-9_.]+)\).*/\1/' | sort | uniq -c | sort -rn | head -25)
  [ -n "$uv" ] && { echo "undeclared values/constructors:"; echo "$uv" | sed 's/^/    /'; }

  te=$(grep -acE "error: Type error" "$LOG")
  if [ "$te" -gt 0 ]; then
    echo "type errors: $te  (sites:)"
    grep -aoE "[A-Za-z0-9_]+\.(sml|sig):[0-9]+: error: Type error" "$LOG" | sed -E 's/: error.*//' | sort -u | head -12 | sed 's/^/    /'
  fi

  sm=$(grep -acE "Structure does not match signature" "$LOG")
  if [ "$sm" -gt 0 ]; then
    echo "signature mismatches: $sm  (sites:)"
    grep -aoE "[A-Za-z0-9_]+\.(sml|sig):[0-9]+: error: Structure does not match" "$LOG" | sed -E 's/: error.*//' | sort -u | head -12 | sed 's/^/    /'
  fi

  se=$(grep -acE "Static Errors" "$LOG")
  [ "$se" -gt 0 ] && echo "Static Errors lines: $se"
  ex=$(grep -aoE "Exception- [A-Za-z_]+" "$LOG" | sort | uniq -c)
  [ -n "$ex" ] && { echo "exceptions:"; echo "$ex" | sed 's/^/    /'; }

  if [ "$nerr" -gt 0 ]; then
    echo
    echo "--- first non-cascade error lines ---"
    grep -aE ": error:|poly: .*error|Exception-" "$LOG" | grep -avE "has not been declared" | head -6 | sed -E 's/^[ >#]*//; s/^/    /'
  fi

  if [ "$TAIL" -gt 0 ]; then
    echo
    echo "--- last $TAIL lines ---"
    tail -"$TAIL" "$LOG" | sed 's/^/    /'
  fi
  echo "=== end (summary saved: $SUM) ==="
} | tee "$SUM"

[ "$RAW" -eq 1 ] && { echo; echo "===== RAW LOG ====="; cat "$LOG"; }

exit $RC
