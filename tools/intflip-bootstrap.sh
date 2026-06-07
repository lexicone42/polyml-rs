#!/usr/bin/env bash
# Run the full PolyML self-bootstrap with arbitrary-precision int enabled
# (--intIsIntInf, read by bootstrap/Stage6.sml). This is the end-to-end test
# of the basis/Real.sml SEGV fix (task #70): Stage6/7 compile the basis under
# arbitrary int, which is where `toArbitrary o realFloor` used to SEGV.
#
# Usage: tools/intflip-bootstrap.sh [out_image]
# Writes progress to /tmp/intflip.log; the chain itself writes `polyexport`.
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
exit $rc
