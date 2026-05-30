#!/usr/bin/env bash
# build-hol4-checkpoints.sh -- build the two warm Poly/ML images the HOL4
# experiments rely on:
#   /tmp/basis_loaded   basis only        (Bootstrap.use "basis/build.sml")
#   /tmp/hol4_kernel    basis + LCF kernel (build_kernel_checkpoint.sml)
#
# Usage: tools/build-hol4-checkpoints.sh [--force] [basis|kernel|all]
#   --force   rebuild even if the image already exists
#   target    which checkpoint(s) to build (default: all)
#
# Env: POLY = poly binary (default <repo>/target/release/poly)
set -uo pipefail

FORCE=0
TARGET=all
while [ $# -gt 0 ]; do
  case "$1" in
    --force) FORCE=1; shift;;
    basis|kernel|all) TARGET="$1"; shift;;
    -h|--help) sed -n '2,12p' "$0"; exit 0;;
    *) echo "unknown arg: $1" >&2; exit 2;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/.." && pwd)"
POLY="${POLY:-$REPO/target/release/poly}"
VPOLY="$REPO/vendor/polyml"
HOL="$REPO/vendor/hol4"
BOOT="$VPOLY/bootstrap/bootstrap64.txt"
SUPPORT="$REPO/crates/polyml-bin/tests/hol4_support"

[ -x "$POLY" ] || { echo "poly not found: $POLY (cargo build --release -p polyml-bin?)" >&2; exit 2; }
[ -f "$BOOT" ] || { echo "bootstrap image not found: $BOOT" >&2; exit 2; }

build_basis() {
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/basis_loaded ]; then
    echo "basis: /tmp/basis_loaded exists ($(wc -c </tmp/basis_loaded) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "basis: building /tmp/basis_loaded …"
  printf 'val () = Bootstrap.use "basis/build.sml";\nval () = PolyML.export("/tmp/basis_loaded", PolyML.rootFunction);\n' \
    | ( cd "$VPOLY" && "$POLY" run --max-steps 10000000000 "$BOOT" ) >/tmp/build-basis.log 2>&1
  if [ -f /tmp/basis_loaded ]; then
    echo "basis: OK ($(wc -c </tmp/basis_loaded) bytes)"
  else
    echo "basis: FAILED — see /tmp/build-basis.log"; tail -5 /tmp/build-basis.log; return 1
  fi
}

build_kernel() {
  [ -f /tmp/basis_loaded ] || { echo "kernel: need /tmp/basis_loaded first"; build_basis || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_kernel ]; then
    echo "kernel: /tmp/hol4_kernel exists ($(wc -c </tmp/hol4_kernel) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "kernel: building /tmp/hol4_kernel …"
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 100000000000 /tmp/basis_loaded \
      < "$SUPPORT/build_kernel_checkpoint.sml" ) >/tmp/build-kernel.log 2>&1
  if [ -f /tmp/hol4_kernel ] && grep -qa "KERNEL_CHECKPOINT_DONE" /tmp/build-kernel.log; then
    echo "kernel: OK ($(wc -c </tmp/hol4_kernel) bytes)"
  else
    echo "kernel: FAILED — see /tmp/build-kernel.log"; tail -8 /tmp/build-kernel.log; return 1
  fi
}

case "$TARGET" in
  basis)  build_basis;;
  kernel) build_kernel;;
  all)    build_basis && build_kernel;;
esac
