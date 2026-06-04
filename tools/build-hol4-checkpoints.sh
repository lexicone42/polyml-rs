#!/usr/bin/env bash
# build-hol4-checkpoints.sh -- build the warm Poly/ML images the HOL4
# experiments rely on, in dependency order:
#   /tmp/basis_loaded   basis only          (Bootstrap.use "basis/build.sml")
#   /tmp/hol4_kernel    basis + LCF kernel   (build_kernel_checkpoint.sml)
#   /tmp/hol4_theory    + Theory subsystem   (theory_subsystem.sml + export)
#   /tmp/hol4_parse     + term/type parser   (build_parse_checkpoint.sml)
#   /tmp/hol4_bool      + bool theory        (build_bool_checkpoint.sml)
#   /tmp/hol4_tactic    + src/1 tactic layer (build_tactic_checkpoint.sml)
#   /tmp/hol4_rewrite   + REWRITE_TAC engine (build_rewrite_checkpoint.sml)
#
# Usage: tools/build-hol4-checkpoints.sh [--force] [basis|kernel|theory|parse|bool|tactic|rewrite|all]
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
    basis|kernel|theory|parse|bool|tactic|rewrite|all) TARGET="$1"; shift;;
    -h|--help) sed -n '2,17p' "$0"; exit 0;;
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

build_theory() {
  [ -f /tmp/hol4_kernel ] || { echo "theory: need /tmp/hol4_kernel first"; build_kernel || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_theory ]; then
    echo "theory: /tmp/hol4_theory exists ($(wc -c </tmp/hol4_theory) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "theory: building /tmp/hol4_theory …"
  # theory_subsystem.sml loads the Theory closure but does not export (it is
  # also driven directly by the hol4_theory tests); append the export tail.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 100000000000 /tmp/hol4_kernel \
      < <( cat "$SUPPORT/theory_subsystem.sml"; \
           printf '\nval () = (print "EXPORTING /tmp/hol4_theory\\n"; PolyML.export("/tmp/hol4_theory", PolyML.rootFunction); print "THEORY_CHECKPOINT_DONE\\n");\n' ) \
    ) >/tmp/build-theory.log 2>&1
  if [ -f /tmp/hol4_theory ] && grep -qa "THEORY_CHECKPOINT_DONE" /tmp/build-theory.log; then
    echo "theory: OK ($(wc -c </tmp/hol4_theory) bytes; $(grep -aoE 'LOADED_OK [0-9]+/[0-9]+' /tmp/build-theory.log | tail -1))"
  else
    echo "theory: FAILED — see /tmp/build-theory.log"; tail -8 /tmp/build-theory.log; return 1
  fi
}

build_parse() {
  [ -f /tmp/hol4_theory ] || { echo "parse: need /tmp/hol4_theory first"; build_theory || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_parse ]; then
    echo "parse: /tmp/hol4_parse exists ($(wc -c </tmp/hol4_parse) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "parse: building /tmp/hol4_parse …"
  # build_parse_checkpoint.sml exports /tmp/hol4_parse itself, gated on a
  # Parse.Term/Parse.Type smoke test (PARSE_SMOKE_PASS).
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_theory \
      < "$SUPPORT/build_parse_checkpoint.sml" ) >/tmp/build-parse.log 2>&1
  if [ -f /tmp/hol4_parse ] && grep -qa "PARSE_CHECKPOINT_DONE" /tmp/build-parse.log; then
    echo "parse: OK ($(wc -c </tmp/hol4_parse) bytes; $(grep -aoE 'LOADED_OK [0-9]+/[0-9]+' /tmp/build-parse.log | tail -1); smoke PASS)"
  else
    echo "parse: FAILED — see /tmp/build-parse.log"; tail -10 /tmp/build-parse.log; return 1
  fi
}

build_bool() {
  [ -f /tmp/hol4_parse ] || { echo "bool: need /tmp/hol4_parse first"; build_parse || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_bool ]; then
    echo "bool: /tmp/hol4_bool exists ($(wc -c </tmp/hol4_bool) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "bool: building /tmp/hol4_bool …"
  # build_bool_checkpoint.sml runs the quote-filter on src/bool/boolScript.sml,
  # builds the bool theory segment, synthesizes `structure boolTheory`, and
  # exports gated on a smoke test (BOOL_SMOKE_PASS).
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_parse \
      < "$SUPPORT/build_bool_checkpoint.sml" ) >/tmp/build-bool.log 2>&1
  if [ -f /tmp/hol4_bool ] && grep -qa "BOOL_CHECKPOINT_DONE" /tmp/build-bool.log; then
    echo "bool: OK ($(wc -c </tmp/hol4_bool) bytes; $(grep -aoE 'BOOLTHEORY_NAMES [0-9]+' /tmp/build-bool.log | tail -1) names; smoke PASS)"
  else
    echo "bool: FAILED — see /tmp/build-bool.log"; tail -10 /tmp/build-bool.log; return 1
  fi
}

build_tactic() {
  [ -f /tmp/hol4_bool ] || { echo "tactic: need /tmp/hol4_bool first"; build_bool || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_tactic ]; then
    echo "tactic: /tmp/hol4_tactic exists ($(wc -c </tmp/hol4_tactic) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "tactic: building /tmp/hol4_tactic …"
  # build_tactic_checkpoint.sml loads the src/1 tactic layer (27 files) and
  # proves p==>p and conj-comm with real tactics; export gated on the smoke.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_bool \
      < "$SUPPORT/build_tactic_checkpoint.sml" ) >/tmp/build-tactic.log 2>&1
  if [ -f /tmp/hol4_tactic ] && grep -qa "TACTIC_CHECKPOINT_DONE" /tmp/build-tactic.log; then
    echo "tactic: OK ($(wc -c </tmp/hol4_tactic) bytes; $(grep -aoE 'TAC_LOADED [0-9]+/[0-9]+' /tmp/build-tactic.log | tail -1); proofs PASS)"
  else
    echo "tactic: FAILED — see /tmp/build-tactic.log"; tail -12 /tmp/build-tactic.log; return 1
  fi
}

build_rewrite() {
  [ -f /tmp/hol4_tactic ] || { echo "rewrite: need /tmp/hol4_tactic first"; build_tactic || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_rewrite ]; then
    echo "rewrite: /tmp/hol4_rewrite exists ($(wc -c </tmp/hol4_rewrite) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "rewrite: building /tmp/hol4_rewrite …"
  # build_rewrite_checkpoint.sml loads BoundedRewrites + Rewrite and proves
  # REWRITE_TAC goals; export gated on REWRITE_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 100000000000 /tmp/hol4_tactic \
      < "$SUPPORT/build_rewrite_checkpoint.sml" ) >/tmp/build-rewrite.log 2>&1
  if [ -f /tmp/hol4_rewrite ] && grep -qa "REWRITE_CHECKPOINT_DONE" /tmp/build-rewrite.log; then
    echo "rewrite: OK ($(wc -c </tmp/hol4_rewrite) bytes; $(grep -aoE 'IMPLICIT_SIZE [0-9]+' /tmp/build-rewrite.log | tail -1); REWRITE_TAC PASS)"
  else
    echo "rewrite: FAILED — see /tmp/build-rewrite.log"; tail -12 /tmp/build-rewrite.log; return 1
  fi
}

case "$TARGET" in
  basis)   build_basis;;
  kernel)  build_kernel;;
  theory)  build_theory;;
  parse)   build_parse;;
  bool)    build_bool;;
  tactic)  build_tactic;;
  rewrite) build_rewrite;;
  all)     build_basis && build_kernel && build_theory && build_parse \
             && build_bool && build_tactic && build_rewrite;;
esac
