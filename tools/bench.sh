#!/usr/bin/env bash
# bench.sh — wall-clock / CPU performance harness for the benchmark corpus.
#
# For each tools/diff-corpus/bench_<name>.sml it runs the LARGE input size on up
# to three engines and prints a comparison table:
#
#   (1) ours          — this repo's ./target/release/poly run <ckpt>   (interpreter)
#   (2) upstream-interp — /tmp/polybuild-interp/poly  (upstream, bytecode backend:
#                         the FAIR interpreter-vs-interpreter comparison)
#   (3) upstream-native — /tmp/polybuild/poly         (upstream native codegen:
#                         the "how far from native" reference)
#
# Timing is CPU time measured INSIDE SML (Timer.startCPUTimer, printed as
# @@time_ms), so it excludes process start-up, image load, and driver
# compilation — it is the pure benchmark compute time and is directly
# comparable across engines. Each measurement is the MINIMUM of REPEAT process
# runs (default 3). BENCH_REPS (default 1) runs the kernel that many times
# inside one timed process (useful for sub-second kernels).
#
# The harness also cross-checks the @@checksum at the LARGE size across all
# available engines and FLAGS any mismatch (faithfulness-at-scale).
#
# Usage:
#   tools/bench.sh                 # all benchmarks, default sizes
#   tools/bench.sh fib sort mmult  # a subset
# Env overrides:
#   POLY_OURS, POLY_CKPT, POLY_UP_INTERP, POLY_UP_NATIVE, POLY_MAXSTEPS,
#   REPEAT (outer min-of-N, default 3), BENCH_REPS (inner reps, default 1),
#   BENCH_SIZE_<name> (override the large N for one benchmark).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CORPUS="$ROOT/tools/diff-corpus"

OURS="${POLY_OURS:-$ROOT/target/release/poly}"
CKPT="${POLY_CKPT:-/tmp/basis_loaded}"
UP_INTERP="${POLY_UP_INTERP:-/tmp/polybuild-interp/poly}"
UP_NATIVE="${POLY_UP_NATIVE:-/tmp/polybuild/poly}"
MAXSTEPS="${POLY_MAXSTEPS:-200000000000}"
REPEAT="${REPEAT:-3}"
BENCH_REPS="${BENCH_REPS:-1}"

# Canonical LARGE input sizes (calibrated so "ours" runs ~1-3 s per rep).
declare -A SIZE=(
  [fib]=35 [tak]=9 [cpstak]=9 [queens]=11 [sieve]=5000000 [sort]=300000
  [mmult]=150 [mandelbrot]=400 [life]=250 [deriv]=2600 [nbody]=350 [ray]=450
)
# Default running order.
ORDER=(fib tak cpstak queens sieve sort mmult mandelbrot life deriv nbody ray)

[ -x "$OURS" ] || { echo "FATAL: ours not found at $OURS (cargo build --release -p polyml-bin)"; exit 2; }
[ -f "$CKPT" ] || { echo "FATAL: checkpoint not found at $CKPT"; exit 2; }

have_interp=0; [ -x "$UP_INTERP" ] && have_interp=1
have_native=0; [ -x "$UP_NATIVE" ] && have_native=1

# Which benchmarks to run.
if [ "$#" -gt 0 ]; then names=("$@"); else names=("${ORDER[@]}"); fi

# extract @@tag from a stream: field(tag)
field() { grep -ao "@@$1=[^[:cntrl:]]*" | head -1 | sed "s/^@@$1=//"; }

# run one engine once; echo "<time_ms> <checksum>"
run_once() {
  local kind="$1" n="$2" file="$3" out
  case "$kind" in
    ours)   out=$(BENCH_TIME=1 BENCH_N="$n" BENCH_REPS="$BENCH_REPS" timeout 300 \
                    "$OURS" run --max-steps "$MAXSTEPS" "$CKPT" < "$file" 2>/dev/null) ;;
    interp) out=$(BENCH_TIME=1 BENCH_N="$n" BENCH_REPS="$BENCH_REPS" timeout 300 \
                    "$UP_INTERP" < "$file" 2>/dev/null) ;;
    native) out=$(BENCH_TIME=1 BENCH_N="$n" BENCH_REPS="$BENCH_REPS" timeout 300 \
                    "$UP_NATIVE" < "$file" 2>/dev/null) ;;
  esac
  local ms cs
  ms=$(printf '%s\n' "$out" | field time_ms)
  cs=$(printf '%s\n' "$out" | field checksum)
  # normalize to per-rep ms
  if [ -n "$ms" ] && [ "$BENCH_REPS" -gt 1 ]; then ms=$(( ms / BENCH_REPS )); fi
  echo "${ms:-NA} ${cs:-NA}"
}

# min-of-REPEAT ms + checksum (from the fastest run)
best() {
  local kind="$1" n="$2" file="$3" i ms cs bestms=NA bestcs=NA
  for ((i=0;i<REPEAT;i++)); do
    read -r ms cs < <(run_once "$kind" "$n" "$file")
    [ "$ms" = NA ] && continue
    if [ "$bestms" = NA ] || [ "$ms" -lt "$bestms" ]; then bestms="$ms"; bestcs="$cs"; fi
  done
  echo "$bestms $bestcs"
}

echo "polyml-rs benchmark performance  ($(date -u +%Y-%m-%dT%H:%MZ))"
echo "  ours          = $OURS run $CKPT"
echo "  upstream-interp = $UP_INTERP  (present=$have_interp)"
echo "  upstream-native = $UP_NATIVE  (present=$have_native)"
echo "  REPEAT=$REPEAT (min)  BENCH_REPS=$BENCH_REPS  metric = in-SML CPU ms (excludes startup)"
echo
printf '%-12s %8s %10s %12s %12s %10s %11s %8s\n' \
  benchmark N ours_ms interp_ms native_ms vs_interp vs_native cksum
printf '%s\n' "-------------------------------------------------------------------------------------------------"

for name in "${names[@]}"; do
  file="$CORPUS/bench_${name}.sml"
  [ -f "$file" ] || { printf '%-12s  (no corpus file)\n' "$name"; continue; }
  ov="BENCH_SIZE_${name}"; n="${!ov:-${SIZE[$name]:-0}}"

  read -r o_ms o_cs   < <(best ours   "$n" "$file")
  i_ms=NA; i_cs=""; n_ms=NA; n_cs=""
  [ "$have_interp" = 1 ] && read -r i_ms i_cs < <(best interp "$n" "$file")
  [ "$have_native" = 1 ] && read -r n_ms n_cs < <(best native "$n" "$file")

  # ratios
  vi=NA; vn=NA
  if [ "$o_ms" != NA ] && [ "$i_ms" != NA ] && [ "$i_ms" -gt 0 ]; then
    vi=$(awk "BEGIN{printf \"%.2f\", $o_ms/$i_ms}"); fi
  if [ "$o_ms" != NA ] && [ "$n_ms" != NA ] && [ "$n_ms" -gt 0 ]; then
    vn=$(awk "BEGIN{printf \"%.2f\", $o_ms/$n_ms}"); fi

  # checksum agreement across present engines
  ck=ok
  for c in "$i_cs" "$n_cs"; do
    [ -n "$c" ] && [ "$c" != NA ] && [ "$c" != "$o_cs" ] && ck=MISMATCH
  done

  printf '%-12s %8s %10s %12s %12s %10s %11s %8s\n' \
    "$name" "$n" "$o_ms" "$i_ms" "$n_ms" "$vi" "$vn" "$ck"
done
echo
echo "vs_interp = ours/upstream-interp CPU-time ratio (>1 = we are slower; the fair interpreter fight)"
echo "vs_native = ours/upstream-native CPU-time ratio (native codegen reference)"
echo "cksum     = LARGE-size @@checksum agreement across all present engines (ok / MISMATCH)"
