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
#   /tmp/hol4_metis     + metisLib (METIS_TAC)  (build_metis_checkpoint.sml)
#
# Usage: tools/build-hol4-checkpoints.sh [--force] [basis|kernel|theory|parse|bool|tactic|rewrite|marker|combin|simp|num|arith|order|prim|relation|all]
#   --force   rebuild even if the image already exists
#   target    which checkpoint(s) to build (default: all)
#
# Env: POLY = poly binary (default <repo>/target/release/poly)
set -uo pipefail

# Checkpoints persist across reboots: the real files live in /var/tmp/polyml-rs
# and the /tmp/* names above are symlinks (tools/persist-ckpts.sh, idempotent).
"$(dirname "$0")/persist-ckpts.sh" || true

FORCE=0
TARGET=all
while [ $# -gt 0 ]; do
  case "$1" in
    --force) FORCE=1; shift;;
    basis|kernel|theory|parse|bool|tactic|rewrite|marker|combin|simp|num|arith|order|prim|relation|taut|meson|metis|all) TARGET="$1"; shift;;
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
  # Built on the PROVER base (/tmp/hol4_metis) so the canonical /tmp/hol4_num has
  # the REAL numTheory AND full bool_ss/SIMP/MESON/METIS live — the unified
  # foundation needed toward the Datatype package (ind_typeTheory's num ancestor).
  [ -f /tmp/hol4_metis ] || { echo "num: need /tmp/hol4_metis first"; build_metis || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_num ]; then
    echo "num: /tmp/hol4_num exists ($(wc -c </tmp/hol4_num) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "num: building /tmp/hol4_num …"
  # build_num_checkpoint.sml builds numTheory from src/num/theories/numScript.sml
  # (bootstraps the naturals + INDUCTION from INFINITY_AX); gated on NUM_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 200000000000 /tmp/hol4_metis \
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

build_prim() {
  [ -f /tmp/hol4_num ] || { echo "prim: need /tmp/hol4_num first"; build_num || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_prim_rec ]; then
    echo "prim: /tmp/hol4_prim_rec exists ($(wc -c </tmp/hol4_prim_rec) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "prim: building /tmp/hol4_prim_rec …"
  # build_prim_rec_checkpoint.sml runs the REAL prim_recScript (Datatype
  # roadmap Stage 1): quote-filtered, TC block + WF tail cut, LESS_LEMMA1 +
  # SIMP_REC + SIMP_REC_THM swapped for the trophy's relationTheory-free
  # proofs. Exports the real prim_recTheory (num_Axiom etc.), smoke-gated.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 400000000000 /tmp/hol4_num \
      < "$SUPPORT/build_prim_rec_checkpoint.sml" ) >/tmp/build-prim.log 2>&1
  if [ -f /tmp/hol4_prim_rec ] && grep -qa "PRIM_REC_CHECKPOINT_DONE" /tmp/build-prim.log; then
    echo "prim: OK ($(wc -c </tmp/hol4_prim_rec) bytes; $(grep -aoE 'PRIMRECTHEORY_NAMES [0-9]+' /tmp/build-prim.log | tail -1) names; num_Axiom present)"
  else
    echo "prim: FAILED — see /tmp/build-prim.log"; tail -12 /tmp/build-prim.log; return 1
  fi
}

build_relation() {
  [ -f /tmp/hol4_prim_rec ] || { echo "relation: need /tmp/hol4_prim_rec first"; build_prim || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_relation ]; then
    echo "relation: /tmp/hol4_relation exists ($(wc -c </tmp/hol4_relation) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "relation: building /tmp/hol4_relation …"
  # build_relation_checkpoint.sml runs the REAL relationScript (Datatype
  # roadmap Stage 2, PARTIAL): full TC/RTC + WF core via real IndDefLib
  # (Inductive RTC -> xHol_reln) with a BasicProvers shim; EQC/WFREC tails
  # skipped (documented in the script). Export gated on the critical names.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 400000000000 /tmp/hol4_prim_rec \
      < "$SUPPORT/build_relation_checkpoint.sml" ) >/tmp/build-relation.log 2>&1
  if [ -f /tmp/hol4_relation ] && grep -qa "RELATION_CHECKPOINT_DONE" /tmp/build-relation.log; then
    echo "relation: core OK ($(grep -aoE 'RELATIONTHEORY_NAMES [0-9]+' /tmp/build-relation.log | tail -1) names) — sweeping the tail …"
    # per-theorem sweep of the remaining ranges (EQC + WFREC + algebra tail);
    # banks whatever proves, then promotes the enriched image over the core.
    ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 1500000000000 /tmp/hol4_relation \
        < "$SUPPORT/relation_tail_sweep.sml" ) >/tmp/build-relation-sweep.log 2>&1
    if [ -f /tmp/hol4_relation_swept ] && grep -qa "SWEEP_DONE" /tmp/build-relation-sweep.log; then
      cat /tmp/hol4_relation_swept > /tmp/hol4_relation
      echo "relation: OK ($(wc -c </tmp/hol4_relation) bytes; $(grep -aoE 'RELATIONTHEORY_NAMES [0-9]+' /tmp/build-relation-sweep.log | tail -1) names after sweep; WFREC/WF_inv_image present)"
    else
      echo "relation: core OK but sweep FAILED — see /tmp/build-relation-sweep.log (keeping core image)"
    fi
  else
    echo "relation: FAILED — see /tmp/build-relation.log"; tail -12 /tmp/build-relation.log; return 1
  fi
}

build_arithmetic() {
  [ -f /tmp/hol4_relation ] || { echo "arithmetic: need /tmp/hol4_relation first"; build_relation || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_arithmetic ]; then
    echo "arithmetic: /tmp/hol4_arithmetic exists ($(wc -c </tmp/hol4_arithmetic) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "arithmetic: sweeping arithmeticScript (Stage 4; 2 passes, re-runnable) …"
  # arithmetic_sweep.sml is re-runnable: CHUNK_HAVE skips saved names; the
  # header new_theory is neutralized when current=arithmetic. Pass 2 flips
  # cascades unlocked by pass 1.
  local base=/tmp/hol4_num
  for pass in 1 2; do
    ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 2000000000000 "$base" \
        < "$SUPPORT/arithmetic_sweep.sml" ) >/tmp/build-arithmetic.log 2>&1
    [ -f /tmp/hol4_arithmetic ] && base=/tmp/hol4_arithmetic
  done
  if [ -f /tmp/hol4_arithmetic ] && grep -qa "ARITHMETIC_SWEEP_DONE" /tmp/build-arithmetic.log; then
    echo "arithmetic: OK ($(wc -c </tmp/hol4_arithmetic) bytes; $(grep -aoE 'ARITHMETICTHEORY_NAMES [0-9]+' /tmp/build-arithmetic.log | tail -1) names)"
  else
    echo "arithmetic: FAILED — see /tmp/build-arithmetic.log"; tail -12 /tmp/build-arithmetic.log; return 1
  fi
}

build_numeral() {
  [ -f /tmp/hol4_arithmetic ] || { echo "numeral: need /tmp/hol4_arithmetic first"; build_arithmetic || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_numeral ]; then
    echo "numeral: /tmp/hol4_numeral exists ($(wc -c </tmp/hol4_numeral) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "numeral: sweeping numeralScript (Stage 4.5) …"
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 2000000000000 /tmp/hol4_arithmetic \
      < "$SUPPORT/numeral_sweep.sml" ) >/tmp/build-numeral.log 2>&1
  if [ -f /tmp/hol4_numeral ] && grep -qa "NUMERAL_SWEEP_DONE" /tmp/build-numeral.log; then
    echo "numeral: OK ($(wc -c </tmp/hol4_numeral) bytes; $(grep -aoE 'NUMERALTHEORY_NAMES [0-9]+' /tmp/build-numeral.log | tail -1) names)"
  else
    echo "numeral: FAILED — see /tmp/build-numeral.log"; tail -12 /tmp/build-numeral.log; return 1
  fi
}

build_numsimps() {
  [ -f /tmp/hol4_numeral ] || { echo "numsimps: need /tmp/hol4_numeral first"; build_numeral || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_numsimps ]; then
    echo "numsimps: /tmp/hol4_numsimps exists ($(wc -c </tmp/hol4_numsimps) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "numsimps: loading the arith dproc + compute stack (Stage 5) …"
  # numSyntax/Num_conv + the src/num/arith/src Presburger stack (ARITH_CONV)
  # + the first-ever computeLib + Arithconv(conv-old)/Boolconv/reduceLib +
  # Cache + numSimps (ARITH_ss). Smoke-gated; exports /tmp/hol4_numsimps.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 2000000000000 /tmp/hol4_numeral \
      < "$SUPPORT/build_numsimps_checkpoint.sml" ) >/tmp/build-numsimps.log 2>&1
  if [ -f /tmp/hol4_numsimps ] && grep -qa "NUMSIMPS_CHECKPOINT_DONE" /tmp/build-numsimps.log; then
    echo "numsimps: OK ($(wc -c </tmp/hol4_numsimps) bytes; ARITH_CONV + ARITH_ss + REDUCE_CONV live)"
  else
    echo "numsimps: FAILED — see /tmp/build-numsimps.log"; tail -12 /tmp/build-numsimps.log; return 1
  fi
}

build_pair() {
  [ -f /tmp/hol4_numsimps ] || { echo "pair: need /tmp/hol4_numsimps first"; build_numsimps || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_pair ]; then
    echo "pair: /tmp/hol4_pair exists ($(wc -c </tmp/hol4_pair) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "pair: sweeping pairScript (Stage 6a — the prod type + TFL prerequisites) …"
  # pairScript: quotientLib is attr-tags only; the prod type is built by
  # new_type_definition. All 18 TFL-critical names land (PAIR/FST/SND/
  # pair_CASES/FORALL_PROD/EXISTS_PROD/pair_induction/UNCURRY/...). The
  # cosmetic SWAP + PAIR_REL relation-algebra family lags (~44 fails) but
  # isn't on the Define path. PAIR_REL_TRANS is skip-listed (GC-churn loop).
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 2000000000000 /tmp/hol4_numsimps \
      < "$SUPPORT/pair_sweep.sml" ) >/tmp/build-pair.log 2>&1
  if [ -f /tmp/hol4_pair ] && grep -qa "PAIR_SWEEP_DONE" /tmp/build-pair.log; then
    echo "pair: OK ($(wc -c </tmp/hol4_pair) bytes; $(grep -aoE 'PAIRTHEORY_NAMES [0-9]+' /tmp/build-pair.log | tail -1) names; prod type + TFL prereqs)"
  else
    echo "pair: FAILED — see /tmp/build-pair.log"; tail -12 /tmp/build-pair.log; return 1
  fi
}

build_defn() {
  # the coretypes chain pair->sum->one->option, then the TFL/Define SML stack.
  [ -f /tmp/hol4_pair ] || { echo "defn: need /tmp/hol4_pair first"; build_pair || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_defn ]; then
    echo "defn: /tmp/hol4_defn exists ($(wc -c </tmp/hol4_defn) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "defn: building the coretypes chain (sum/one/option) + TFL/Define stack (Stage 6b) …"
  local S="$SUPPORT"
  # sum on pair, one on sum, option on one (each Script->Theory sweep)
  for step in "sum:hol4_pair:sum_sweep:SUM_SWEEP_DONE" \
              "one:hol4_sum:one_sweep:ONE_SWEEP_DONE" \
              "option:hol4_one:option_sweep:OPTION_SWEEP_DONE"; do
    local nm="${step%%:*}"; local rest="${step#*:}"
    local base="${rest%%:*}"; rest="${rest#*:}"
    local script="${rest%%:*}"; local marker="${rest##*:}"
    if [ "$FORCE" -eq 1 ] || [ ! -f "/tmp/hol4_$nm" ]; then
      ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 2000000000000 "/tmp/$base" \
          < "$S/$script.sml" ) >"/tmp/build-$nm.log" 2>&1
      grep -qa "$marker" "/tmp/build-$nm.log" || { echo "defn: $nm sweep FAILED — /tmp/build-$nm.log"; tail -8 "/tmp/build-$nm.log"; return 1; }
      echo "defn:   $nm OK ($(grep -aoE '[A-Z]+THEORY_NAMES [0-9]+' /tmp/build-$nm.log | tail -1))"
    fi
  done
  # the TFL/Define SML stack on /tmp/hol4_option -> /tmp/hol4_defn
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 600000000000 /tmp/hol4_option \
      < "$S/build_defn_checkpoint.sml" ) >/tmp/build-defn.log 2>&1
  if [ -f /tmp/hol4_defn ] && grep -qa "DEFN_CHECKPOINT_DONE" /tmp/build-defn.log; then
    echo "defn: OK ($(wc -c </tmp/hol4_defn) bytes; Define runs — recursive + auto-termination)"
  else
    echo "defn: FAILED — see /tmp/build-defn.log"; tail -12 /tmp/build-defn.log; return 1
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

build_metis() {
  [ -f /tmp/hol4_meson ] || { echo "metis: need /tmp/hol4_meson first"; build_meson || return 1; }
  if [ "$FORCE" -eq 0 ] && [ -f /tmp/hol4_metis ]; then
    echo "metis: /tmp/hol4_metis exists ($(wc -c </tmp/hol4_metis) bytes) — skip (--force to rebuild)"
    return 0
  fi
  echo "metis: building /tmp/hol4_metis …"
  # build_metis_checkpoint.sml builds the full bool_ss closure, the 33-module mlib*
  # prover core, normalForms+folTools, and metisLib; METIS_TAC then proves
  # equality/paramodulation goals (AC_CHAIN, CONG). Export gated on METIS_SMOKE_PASS.
  ( cd "$VPOLY" && HOL4_DIR="$HOL" "$POLY" run --max-steps 800000000000 /tmp/hol4_meson \
      < "$SUPPORT/build_metis_checkpoint.sml" ) >/tmp/build-metis.log 2>&1
  if [ -f /tmp/hol4_metis ] && grep -qa "METIS_CHECKPOINT_DONE" /tmp/build-metis.log; then
    echo "metis: OK ($(wc -c </tmp/hol4_metis) bytes; $(grep -aoE 'METIS AC_CHAIN:.*' /tmp/build-metis.log | head -1 | cut -c1-60))"
  else
    echo "metis: FAILED — see /tmp/build-metis.log"; tail -12 /tmp/build-metis.log; return 1
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
  prim)    build_prim;;
  relation) build_relation;;
  arithmetic) build_arithmetic;;
  numeral) build_numeral;;
  numsimps) build_numsimps;;
  pair)    build_pair;;
  defn)    build_defn;;
  taut)    build_taut;;
  meson)   build_meson;;
  metis)   build_metis;;
  all)     build_basis && build_kernel && build_theory && build_parse \
             && build_bool && build_tactic && build_rewrite && build_marker \
             && build_combin && build_simp && build_taut && build_meson \
             && build_metis && build_num && build_arith && build_order \
             && build_prim && build_relation;;
esac
