#!/usr/bin/env bash
# build-oracle.sh — build the REAL upstream PolyML as a ground-truth oracle for
# differential testing (tools/diff-oracle.sh). Out-of-tree so vendor/polyml stays
# pristine. The resulting binary is the authority on SML semantics; any output
# difference between it and our `poly run` is a faithfulness bug in OUR port.
#
# Default int config of the built oracle: FixedInt 63-bit (Int.maxInt =
# 4611686018427387903, Int.precision = 63) — which MATCHES our /tmp/basis_loaded
# checkpoint, so that checkpoint is the right one to diff against. (Our
# /tmp/arbint_image uses arbitrary-precision int and would mismatch.)
#
#   tools/build-oracle.sh            # builds to /tmp/polybuild/poly
#   POLY_BUILD_DIR=/path tools/build-oracle.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/vendor/polyml"
BUILD="${POLY_BUILD_DIR:-/tmp/polybuild}"

[ -x "$SRC/configure" ] || { echo "FATAL: $SRC/configure missing (vendor/polyml not present)"; exit 2; }
command -v g++  >/dev/null || { echo "FATAL: g++ not found"; exit 2; }
command -v make >/dev/null || { echo "FATAL: make not found"; exit 2; }

echo "=== configuring upstream PolyML (out-of-tree: $BUILD) ==="
rm -rf "$BUILD"; mkdir -p "$BUILD"; cd "$BUILD"
"$SRC/configure" --prefix="$BUILD/install" > "$BUILD/configure.log" 2>&1

echo "=== building (self-bootstrap; several minutes) ==="
make -j"$(nproc)" > "$BUILD/make.log" 2>&1

if [ -x "$BUILD/poly" ]; then
  echo "=== OK: oracle at $BUILD/poly ==="
  echo 'val()=print("Int.maxInt="^(case Int.maxInt of NONE=>"NONE"|SOME n=>Int.toString n)^"\n");' | "$BUILD/poly" 2>&1 | grep -o 'Int.maxInt=.*' || true
else
  echo "FATAL: build did not produce $BUILD/poly — see $BUILD/make.log"; tail -20 "$BUILD/make.log"; exit 1
fi
