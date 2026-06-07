#!/usr/bin/env bash
# Run the full PolyML self-bootstrap with arbitrary-precision int enabled
# (--intIsIntInf, read by bootstrap/Stage6.sml) and stage the resulting image at
# /tmp/arbint_image. This is THE arbitrary-precision int flip: our interpreter
# self-compiles a PolyML image whose default `int` is arbitrary precision
# (Int.precision = NONE) — the keystone Isabelle (#69) requires. Cleared by
# implementing the Real-math RTS + the REAL_TO_FLOAT operand-byte fix (commit
# 7fa5090) + the arbitrary-int RTS/shift fixes.
#
# Usage: tools/intflip-bootstrap.sh
# Progress -> /tmp/intflip.log; final image -> /tmp/arbint_image (and the chain's
# own vendor/polyml/polyexport). Gated on a default-int=arbitrary smoke test.
set -u
cd "$(dirname "$0")/../vendor/polyml" || exit 1
POLY=../../target/release/poly
LOG=/tmp/intflip.log
: > "$LOG"
echo "intflip: starting full Stage1 chain with --intIsIntInf …" | tee -a "$LOG"
POLYML_GC_QUIET=1 "$POLY" run --max-steps 200000000000 \
    bootstrap/bootstrap64.txt -- -I . --intIsIntInf \
    < bootstrap/Stage1.sml >> "$LOG" 2>&1
rc=$?
echo "intflip: exit $rc" | tee -a "$LOG"
[ "$rc" -ne 0 ] && exit $rc
[ -f polyexport ] || { echo "intflip: no polyexport produced" | tee -a "$LOG"; exit 1; }
cp polyexport /tmp/arbint_image
# Smoke: the new image's default int must be arbitrary precision.
smoke=$(printf 'val()=print("PREC="^(case Int.precision of NONE=>"NONE" | SOME n=>Int.toString n)^"\\n");' \
    | POLYML_GC_QUIET=1 "$POLY" run --max-steps 2000000000 /tmp/arbint_image 2>/dev/null \
    | grep -oE 'PREC=[A-Za-z0-9]+')
echo "intflip: /tmp/arbint_image staged ($(stat -c%s /tmp/arbint_image) bytes); $smoke" | tee -a "$LOG"
[ "$smoke" = "PREC=NONE" ] || { echo "intflip: SMOKE FAILED (expected PREC=NONE)" | tee -a "$LOG"; exit 1; }
echo "intflip: OK — arbitrary-precision int image ready at /tmp/arbint_image" | tee -a "$LOG"
exit 0
