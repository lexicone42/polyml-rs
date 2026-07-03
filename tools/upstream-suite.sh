#!/usr/bin/env bash
# upstream-suite.sh — run Poly/ML's OWN regression corpus
# (vendor/polyml/Tests: Succeed/ must compile+run clean, Fail/ must fail
# to compile) through our interpreter, ONE PROCESS PER TEST.
#
# Per-process isolation matters: a few upstream tests exercise conditions
# our interpreter turns into HARD halts rather than catchable SML
# exceptions (e.g. deep recursion → "stack overflow" halt, where upstream
# grows ML stacks dynamically). In-process driving (upstream's
# RunTests.sml) dies at the first such test; per-process, it just fails
# that one test and the tally stays honest.
#
# `NotApplicable` follows upstream RunTests.sml semantics: a test raising
# it is treated as passing (platform-specific tests).
#
# Usage: tools/upstream-suite.sh [succeed|fail|all]   (default: all)
# Output: per-test PASS/FAIL lines + a final tally; failures listed.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
POLY="${POLY:-$ROOT/target/release/poly}"
VENDOR="$ROOT/vendor/polyml"
IMAGE="$VENDOR/polyexport"
MODE="${1:-all}"

[ -x "$POLY" ] || { echo "missing poly binary: $POLY"; exit 2; }
[ -f "$IMAGE" ] || { echo "missing $IMAGE (self-bootstrap first)"; exit 2; }

run_one() { # file expect_success
    local f="$1" expect="$2" out rc
    local driver
    driver=$(mktemp /tmp/upstream_one_XXXX.sml)
    cat > "$driver" <<EOF
exception NotApplicable;
val () =
  (PolyML.use "$f"; print "\nONE_RESULT compiled\n")
  handle NotApplicable => print "\nONE_RESULT notapplicable\n"
       | _ => print "\nONE_RESULT raised\n";
EOF
    out=$(cd "$VENDOR" && POLYML_GC_QUIET=1 timeout 120 "$POLY" run \
        --max-steps 20000000000 "$IMAGE" < "$driver" 2>&1)
    rc=$?
    rm -f "$driver"
    local verdict
    if echo "$out" | grep -q "ONE_RESULT compiled"; then verdict=compiled
    elif echo "$out" | grep -q "ONE_RESULT notapplicable"; then verdict=notapplicable
    elif echo "$out" | grep -q "ONE_RESULT raised"; then verdict=raised
    else verdict="halted(rc=$rc)"   # hard halt / timeout / crash
    fi
    if [ "$expect" = yes ]; then
        case "$verdict" in
            compiled|notapplicable) echo PASS;;
            *) echo "FAIL($verdict)";;
        esac
    else
        # Fail tests: the compile/run must NOT succeed.
        case "$verdict" in
            compiled) echo "FAIL(unexpected-success)";;
            notapplicable) echo PASS;;
            raised) echo PASS;;
            *) echo "FAIL($verdict)";;
        esac
    fi
}

pass=0; fail=0; failed_list=()
run_dir() { # dir expect
    local dir="$1" expect="$2" f v
    for f in "$VENDOR/Tests/$dir"/*.ML; do
        local rel="Tests/$dir/$(basename "$f")"
        v=$(run_one "$rel" "$expect")
        printf '%-40s %s\n' "$rel" "$v"
        if [ "$v" = PASS ]; then pass=$((pass+1)); else
            fail=$((fail+1)); failed_list+=("$rel:$v"); fi
    done
}

case "$MODE" in
    succeed) run_dir Succeed yes;;
    fail)    run_dir Fail no;;
    all)     run_dir Succeed yes; run_dir Fail no;;
    *) echo "usage: $0 [succeed|fail|all]"; exit 2;;
esac

echo
echo "=== upstream suite: $pass passed, $fail failed ==="
if [ "$fail" -gt 0 ]; then
    printf '%s\n' "${failed_list[@]}"
fi
[ "$fail" -eq 0 ]
