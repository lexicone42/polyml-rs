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
#   /tmp/hol4_marker    + markerTheory       (build_marker_checkpoint.sml)
#   /tmp/hol4_combin    + combinTheory       (build_combin_checkpoint.sml)
#   /tmp/hol4_simp      + simpLib SIMP_TAC   (build_simp_checkpoint.sml)
#   /tmp/hol4_num       + numTheory          (build_num_checkpoint.sml)
#   /tmp/hol4_arith     + arithmetic (+,*,EVEN) (build_arith_checkpoint.sml)
#   /tmp/hol4_taut      + HolSat/tautLib (DPLL) (build_taut_checkpoint.sml)
#   /tmp/hol4_meson     + mesonLib (MESON_TAC)  (build_meson_checkpoint.sml)
#
# Usage: tools/build-hol4-checkpoints.sh [--force] [basis|kernel|theory|parse|bool|tactic|rewrite|marker|combin|simp|num|arith|order|all]
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
    basis|kernel|theory|parse|bool|tactic|rewrite|marker|combin|simp|num|arith|order|taut|meson|all) TARGET="$1"; shift;;
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

build_marker() {
  [ -f /tmp/hol4_rewrite ] || { echo "marker: need /tmp/hol4_rewrite first"; build_rewrite || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_marker ]; then
    echo "marker: /tmp/hol4_marker exists ($(wc -c </tmp/hol4_marker) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "marker: building /tmp/hol4_marker …"
  # build_marker_checkpoint.sml builds markerTheory from src/marker/markerScript.sml
  # (the first *Script theory on a NON-empty base); export gated on MARKER_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_rewrite \
      < "$SUPPORT/build_marker_checkpoint.sml" ) >/tmp/build-marker.log 2>&1
  if [ -f /tmp/hol4_marker ] && grep -qa "MARKER_CHECKPOINT_DONE" /tmp/build-marker.log; then
    echo "marker: OK ($(wc -c </tmp/hol4_marker) bytes; $(grep -aoE 'MARKERTHEORY_NAMES [0-9]+' /tmp/build-marker.log | tail -1) names; smoke PASS)"
  else
    echo "marker: FAILED — see /tmp/build-marker.log"; tail -12 /tmp/build-marker.log; return 1
  fi
}

build_combin() {
  [ -f /tmp/hol4_marker ] || { echo "combin: need /tmp/hol4_marker first"; build_marker || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_combin ]; then
    echo "combin: /tmp/hol4_combin exists ($(wc -c </tmp/hol4_combin) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "combin: building /tmp/hol4_combin …"
  # build_combin_checkpoint.sml builds combinTheory from src/combin/combinScript.sml
  # (Libs ... computeLib stubbed; Q loaded); export gated on COMBIN_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_marker \
      < "$SUPPORT/build_combin_checkpoint.sml" ) >/tmp/build-combin.log 2>&1
  if [ -f /tmp/hol4_combin ] && grep -qa "COMBIN_CHECKPOINT_DONE" /tmp/build-combin.log; then
    echo "combin: OK ($(wc -c </tmp/hol4_combin) bytes; $(grep -aoE 'COMBINTHEORY_NAMES [0-9]+' /tmp/build-combin.log | tail -1) names; smoke PASS)"
  else
    echo "combin: FAILED — see /tmp/build-combin.log"; tail -12 /tmp/build-combin.log; return 1
  fi
}

build_simp() {
  [ -f /tmp/hol4_combin ] || { echo "simp: need /tmp/hol4_combin first"; build_combin || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_simp ]; then
    echo "simp: /tmp/hol4_simp exists ($(wc -c </tmp/hol4_simp) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "simp: building /tmp/hol4_simp …"
  # build_simp_checkpoint.sml assembles simpLib (leaves + 5 core + markerLib/
  # TypeBase stubs) and proves a goal via SIMP_CONV+SIMP_TAC; gated on SIMP_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_combin \
      < "$SUPPORT/build_simp_checkpoint.sml" ) >/tmp/build-simp.log 2>&1
  if [ -f /tmp/hol4_simp ] && grep -qa "SIMP_CHECKPOINT_DONE" /tmp/build-simp.log; then
    echo "simp: OK ($(wc -c </tmp/hol4_simp) bytes; $(grep -aoE 'TOTAL [0-9]+/[0-9]+' /tmp/build-simp.log | tail -1) loaded; SIMP_TAC PASS)"
  else
    echo "simp: FAILED — see /tmp/build-simp.log"; tail -12 /tmp/build-simp.log; return 1
  fi
}

build_num() {
  [ -f /tmp/hol4_combin ] || { echo "num: need /tmp/hol4_combin first"; build_combin || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_num ]; then
    echo "num: /tmp/hol4_num exists ($(wc -c </tmp/hol4_num) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "num: building /tmp/hol4_num …"
  # build_num_checkpoint.sml builds numTheory from src/num/theories/numScript.sml
  # (bootstraps the naturals + INDUCTION from INFINITY_AX); gated on NUM_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_combin \
      < "$SUPPORT/build_num_checkpoint.sml" ) >/tmp/build-num.log 2>&1
  if [ -f /tmp/hol4_num ] && grep -qa "NUM_CHECKPOINT_DONE" /tmp/build-num.log; then
    echo "num: OK ($(wc -c </tmp/hol4_num) bytes; $(grep -aoE 'NUMTHEORY_NAMES [0-9]+' /tmp/build-num.log | tail -1) names; INDUCTION present; smoke PASS)"
  else
    echo "num: FAILED — see /tmp/build-num.log"; tail -12 /tmp/build-num.log; return 1
  fi
}

build_arith() {
  [ -f /tmp/hol4_num ] || { echo "arith: need /tmp/hol4_num first"; build_num || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_arith ]; then
    echo "arith: /tmp/hol4_arith exists ($(wc -c </tmp/hol4_arith) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "arith: building /tmp/hol4_arith …"
  # build_arith_checkpoint.sml derives num_Axiom + add + mult and proves the
  # Peano laws (ADD_COMM/ASSOC, MULT_COMM, distrib, cancellation, parity) by
  # induction; export gated on a hypothesis-free smoke check.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 400000000000 /tmp/hol4_num \
      < "$SUPPORT/build_arith_checkpoint.sml" ) >/tmp/build-arith.log 2>&1
  if [ -f /tmp/hol4_arith ] && grep -qa "ARITH_CHECKPOINT_DONE" /tmp/build-arith.log; then
    echo "arith: OK ($(wc -c </tmp/hol4_arith) bytes; $(grep -aoE 'SMOKE_ADD_COMM:.*' /tmp/build-arith.log | head -1))"
  else
    echo "arith: FAILED — see /tmp/build-arith.log"; tail -12 /tmp/build-arith.log; return 1
  fi
}

build_order() {
  [ -f /tmp/hol4_num ] || { echo "order: need /tmp/hol4_num first"; build_num || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_order ]; then
    echo "order: /tmp/hol4_order exists ($(wc -c </tmp/hol4_order) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "order: building /tmp/hol4_order …"
  # build_order_checkpoint.sml defines LE (m<=n <=> ?p. n = m+p) and proves the
  # ordering laws (refl/trans/antisym/...) by induction; export gated on smoke.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 400000000000 /tmp/hol4_num \
      < "$SUPPORT/build_order_checkpoint.sml" ) >/tmp/build-order.log 2>&1
  if [ -f /tmp/hol4_order ] && grep -qa "ORDER_CHECKPOINT_DONE" /tmp/build-order.log; then
    echo "order: OK ($(wc -c </tmp/hol4_order) bytes; $(grep -aoE 'SMOKE_LE_ANTISYM:.*' /tmp/build-order.log | head -1))"
  else
    echo "order: FAILED — see /tmp/build-order.log"; tail -12 /tmp/build-order.log; return 1
  fi
}

build_taut() {
  [ -f /tmp/hol4_combin ] || { echo "taut: need /tmp/hol4_combin first"; build_combin || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_taut ]; then
    echo "taut: /tmp/hol4_taut exists ($(wc -c </tmp/hol4_taut) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "taut: building /tmp/hol4_taut …"
  # build_taut_checkpoint.sml builds satTheory (truth-table tautologies) and
  # loads the HolSat closure + tautLib; TAUT_PROVE runs via the pure-SML DPLL
  # solver (no external minisat — access(solverExe) is false). Needs the
  # OS.FileSys.tmpName/remove RTS support. Export gated on TAUT_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_combin \
      < "$SUPPORT/build_taut_checkpoint.sml" ) >/tmp/build-taut.log 2>&1
  if [ -f /tmp/hol4_taut ] && grep -qa "TAUT_CHECKPOINT_DONE" /tmp/build-taut.log; then
    echo "taut: OK ($(wc -c </tmp/hol4_taut) bytes; $(grep -aoE 'TAUT_RESULT [A-Z_]+:.*' /tmp/build-taut.log | head -1))"
  else
    echo "taut: FAILED — see /tmp/build-taut.log"; tail -12 /tmp/build-taut.log; return 1
  fi
}

build_meson() {
  [ -f /tmp/hol4_simp ] || { echo "meson: need /tmp/hol4_simp first"; build_simp || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_meson ]; then
    echo "meson: /tmp/hol4_meson exists ($(wc -c </tmp/hol4_meson) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "meson: building /tmp/hol4_meson …"
  # build_meson_checkpoint.sml replays the taut layer on simp (widened boolLib +
  # satTheory + HolSat + tautLib) then loads Canon_Port/jrhTactics/mesonLib and
  # runs MESON_TAC proofs (first-order, via DPLL-backed tautLib). Export gated on
  # MESON_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 400000000000 /tmp/hol4_simp \
      < "$SUPPORT/build_meson_checkpoint.sml" ) >/tmp/build-meson.log 2>&1
  if [ -f /tmp/hol4_meson ] && grep -qa "MESON_CHECKPOINT_DONE" /tmp/build-meson.log; then
    echo "meson: OK ($(wc -c </tmp/hol4_meson) bytes; $(grep -aoE 'MESON DRINKER:.*' /tmp/build-meson.log | head -1))"
  else
    echo "meson: FAILED — see /tmp/build-meson.log"; tail -12 /tmp/build-meson.log; return 1
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
  marker)  build_marker;;
  combin)  build_combin;;
  simp)    build_simp;;
  num)     build_num;;
  arith)   build_arith;;
  order)   build_order;;
  taut)    build_taut;;
  meson)   build_meson;;
  all)     build_basis && build_kernel && build_theory && build_parse \
             && build_bool && build_tactic && build_rewrite && build_marker \
             && build_combin && build_simp && build_num && build_arith \
             && build_order && build_taut && build_meson;;
esac
