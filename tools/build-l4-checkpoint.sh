#!/usr/bin/env bash
# Build the WARM Lagrange-four-square base checkpoint at /tmp/l4_foursq_star
# (symlinked into the persistent store like the other checkpoints).
#
# Lagrange's four-square theorem (forall n. EX a b c d. n = a^2+b^2+c^2+d^2) is
# proved in two stages because the proof's working set is large:
#
#   1. THIS script loads the four-square *base* — the classical-FOL number-theory
#      ladder + Euler's four-square identity (four_sq_mult), lagrange_assembly,
#      the signed-residue keystone, and all the descent helpers — on top of the
#      warm Isabelle/Pure checkpoint, then PolyML.export's a checkpoint so the
#      heavy proof can start from a loaded context in seconds. It banks
#      `restore_l4_context` (the generic context is thread-local and lost on
#      reload; reloaders call it before proving) exactly as build-isabelle-pure.sh
#      banks `restore_pure_context`.
#
#   2. The FULL driver (tests/isabelle_support/four_square_resume/
#      lagrange_four_square_FULL_driver.sml) then runs ON this checkpoint and
#      closes the theorem: the 9 Euler divide-by-m^2 leaves -> the 16->9 disjE
#      descent step -> strict r<m -> strong-induction iteration to m=1 ->
#      discharge lagrange_assembly. It is driven by the #[ignore] test
#      `four_square_full_theorem` in tests/isabelle_four_square.rs.
#
# Prereqs: /tmp/isabelle_pure (tools/build-isabelle-pure.sh).
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
POLY="$ROOT/target/release/poly"
IMG=/tmp/isabelle_pure
SUP="$ROOT/crates/polyml-bin/tests/isabelle_support/four_square_resume"
BASE="$SUP/_assembled_base.sml"
# seat1 defines the descent helpers the leaves use (cong_radd_cancel_r,
# dvd_of_cong_zero, ...) and proves descent_residue; it runs inline on the
# assembled base (no restore_l4_context).
SEAT1="$SUP/seat1_descent_residue_delta.sml"
OUT="${1:-/tmp/l4_foursq_star}"

[ -f "$POLY" ]  || { echo "missing $POLY — cargo build --release -p polyml-bin"; exit 1; }
[ -f "$IMG" ]   || { echo "missing $IMG — run tools/build-isabelle-pure.sh"; exit 1; }
[ -f "$BASE" ]  || { echo "missing $BASE"; exit 1; }
[ -f "$SEAT1" ] || { echo "missing $SEAT1"; exit 1; }

DRIVER=/tmp/build_l4_checkpoint_driver.sml
{
  # Proof-TERM recording off: bounds RAM. The kernel STILL validates every
  # inference, so exported theorems remain genuine (standard Isabelle practice).
  echo 'val () = (Proofterm.proofs := 0);'
  cat "$BASE"
  echo ''
  echo '(* ---- descent helpers (cong_radd_cancel_r, dvd_of_cong_zero, ...) ---- *)'
  cat "$SEAT1"
  echo ''
  # Bank `star_v`: the (star) all-positive Euler 4-square identity proved at 8
  # DISTINCT schematic vars sa_v..sh_v and varified, so the divide leaves can
  # cheaply infer_instantiate it instead of re-running the ~13-min full monomial
  # expansion per leaf. proveStarFor + varify come from the assembled base.
  echo '(* ---- bank star_v (the varified general Euler star identity) ---- *)'
  cat <<'SML'
val star_v =
  let
    val a = Free("sa_v",natT); val b = Free("sb_v",natT);
    val c = Free("sc_v",natT); val d = Free("sd_v",natT);
    val e = Free("se_v",natT); val f = Free("sf_v",natT);
    val g = Free("sg_v",natT); val h = Free("sh_v",natT)
  in varify (proveStarFor (a,b,c,d,e,f,g,h)) end;
val () = out ("L4_STAR_V_BANKED hyps="^Int.toString(length(Thm.hyps_of star_v))^"\n");
SML
  echo '(* ---- bank the L4 generic context + SML bindings, export checkpoint ---- *)'
  echo 'val L4_context = Context.the_generic_context ();'
  echo 'fun restore_l4_context () = Context.put_generic_context (SOME L4_context);'
  echo "val () = (PolyML.export (\"$OUT\", PolyML.rootFunction); out \"L4_CHECKPOINT_DONE\\n\");"
} > "$DRIVER"

echo "building four-square base checkpoint -> $OUT (loading the NT ladder + four_sq_mult, a few min) ..."
( cd "$ROOT/vendor/polyml" && ML_SYSTEM=polyml ML_PLATFORM=x86_64-linux ISABELLE_HOME=/tmp/isa \
    POLYML_GC_QUIET=1 POLYML_GC_THRESHOLD=99 POLYML_HEAP_BYTES=8000000000 \
    "$POLY" run --max-steps 300000000000 "$IMG" < "$DRIVER" ) 2>&1 \
  | grep -aE "FOUNDATION_OK|L4_BASE_OK|L4_.*_OK|L4_CHECKPOINT_DONE|Static Errors|Exception-"

if [ -f "$OUT" ]; then
  echo "l4-checkpoint: OK ($(wc -c <"$OUT") bytes)"
  [ -x "$ROOT/tools/persist-ckpts.sh" ] && "$ROOT/tools/persist-ckpts.sh" >/dev/null 2>&1 || true
else
  echo "l4-checkpoint: FAILED (no $OUT)"; exit 1
fi
