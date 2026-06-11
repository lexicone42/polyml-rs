#!/usr/bin/env bash
# persist-ckpts.sh — make the /tmp checkpoint + oracle artifacts survive reboots.
#
# Everything in this repo (scripts, tests, docs, muscle memory) refers to
# /tmp/basis_loaded, /tmp/hol4_*, /tmp/polybuild/... — but /tmp is wiped on
# reboot/power-loss, which costs ~an hour of rebuilds. Rather than rewriting
# every path, this script keeps the real artifacts in a persistent store
# (/var/tmp persists across reboots per FHS) and points /tmp symlinks at them:
#
#   - an existing REAL file in /tmp is migrated into the store (first run);
#   - a /tmp symlink is (re)created for every known artifact name, so builders
#     that write "/tmp/basis_loaded" write through the link into the store;
#   - after a reboot (links gone, store intact) re-running this restores
#     everything instantly — no rebuilds.
#
# Idempotent; called automatically by build-hol4-checkpoints.sh. Run manually
# after a reboot:   tools/persist-ckpts.sh
# Override store:   POLYML_CKPT_DIR=/elsewhere tools/persist-ckpts.sh
set -uo pipefail
STORE="${POLYML_CKPT_DIR:-/var/tmp/polyml-rs}"
mkdir -p "$STORE"

# Checkpoint images (PolyML.export outputs) + the arbitrary-int basis image.
ARTIFACTS=(
  basis_loaded arbint_image
  hol4_kernel hol4_theory hol4_parse hol4_bool hol4_tactic hol4_rewrite
  hol4_marker hol4_combin hol4_simp hol4_taut hol4_meson hol4_metis
  hol4_num hol4_arith hol4_order hol4_prim_rec hol4_relation hol4_arithmetic hol4_numeral hol4_numsimps hol4_pair hol4_sum hol4_one hol4_option hol4_defn hol4_numpair hol4_ind_type
)

migrated=0; linked=0; kept=0
for a in "${ARTIFACTS[@]}"; do
  tmp="/tmp/$a"; dst="$STORE/$a"
  if [ -f "$tmp" ] && [ ! -L "$tmp" ]; then
    mv "$tmp" "$dst" && migrated=$((migrated+1))
  fi
  if [ -L "$tmp" ]; then
    [ "$(readlink "$tmp")" = "$dst" ] && { kept=$((kept+1)); continue; }
    rm -f "$tmp"
  fi
  ln -s "$dst" "$tmp" && linked=$((linked+1))
done

# Oracle build trees (directories). Same treatment: migrate real dirs, link.
# build-oracle.sh builds directly into the store (see its BUILD default);
# these links keep the historical /tmp/polybuild* paths readable.
for d in polybuild polybuild-interp; do
  tmp="/tmp/$d"; dst="$STORE/$d"
  if [ -d "$tmp" ] && [ ! -L "$tmp" ]; then
    rm -rf "$dst"; mv "$tmp" "$dst" && migrated=$((migrated+1))
  fi
  if [ -L "$tmp" ]; then
    [ "$(readlink "$tmp")" = "$dst" ] && { kept=$((kept+1)); continue; }
    rm -f "$tmp"
  fi
  ln -s "$dst" "$tmp" && linked=$((linked+1))
done

present=0
for a in "${ARTIFACTS[@]}"; do [ -f "$STORE/$a" ] && present=$((present+1)); done
echo "persist-ckpts: store=$STORE  migrated=$migrated linked=$linked kept=$kept; $present/${#ARTIFACTS[@]} checkpoints present in store"
[ -x "$STORE/polybuild/poly" ] && echo "persist-ckpts: native oracle present" || echo "persist-ckpts: native oracle ABSENT (tools/build-oracle.sh)"
[ -x "$STORE/polybuild-interp/poly" ] && echo "persist-ckpts: interp oracle present" || echo "persist-ckpts: interp oracle ABSENT (tools/build-oracle.sh interp)"
