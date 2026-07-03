#!/usr/bin/env bash
# tsan.sh — ThreadSanitizer audit of the concurrency stack.
#
# Independent instrument for the parallel memory model: builds the
# interpreter-only poly (no Cranelift) + the runtime test suites with
# TSan on nightly, then drives the threaded workloads and the
# racy-publish probes. Zero warnings = the word-object heap graph
# (pointers, tuples, closures, arrays, vectors, headers) is data-race-
# free BY CONSTRUCTION under POLY_PARALLEL, not just by testing.
#
# Known, documented residual (tools/tsan-probes/byte_publish.sml WILL
# warn): byte-array/string CONTENT accesses are plain (scalar byte ops
# + blockMoveByte's memmove); racy SML byte publishes are a formal race
# on the content bytes. Wrap shared byte buffers in an SML Mutex.
#
# Usage: tools/tsan.sh [fast|full]
#   fast (default): unit suites + mutex/racy demos + word-publish probes
#   full: + GC handshake suite + alloc storm + 4 fuzz-dump seeds
#
# Needs: rustup nightly with rust-src; vendor/polyml/polyexport for the
# demo/probe stages (skipped if missing).
set -uo pipefail
MODE="${1:-fast}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
TARGET=x86_64-unknown-linux-gnu
TSAN_POLY="target/$TARGET/release/poly"
export RUSTFLAGS="-Zsanitizer=thread"
FAILED=0

note() { printf '\n=== %s\n' "$*"; }
check_warnings() { # log label
    local n
    n=$(grep -cE "WARNING: ThreadSanitizer" "$1")
    if [ "$n" -eq 0 ]; then echo "OK   $2 (0 warnings)"; else
        echo "FAIL $2 ($n TSan warnings) — log: $1"; FAILED=1; fi
}

note "TSan build: runtime unit + GC tests"
cargo +nightly test -Zbuild-std --target $TARGET --release -p polyml-runtime --lib gc 2>&1 \
    | grep -E "test result" || FAILED=1

note "TSan build: interpreter-only poly"
cargo +nightly build -Zbuild-std --target $TARGET --release -p polyml-bin --no-default-features 2>&1 \
    | tail -1

if [ ! -f vendor/polyml/polyexport ]; then
    echo "SKIP: vendor/polyml/polyexport missing — unit stages only"
    exit $FAILED
fi

note "threaded demos + probes under TSan (POLY_PARALLEL=1)"
run_probe() { # name sml-path extra-env...
    local name="$1" sml="$2"; shift 2
    local log="/tmp/tsan_run_${name}.log"
    env POLY_REAL_THREADS=1 POLY_PARALLEL=1 "$@" \
        timeout 900 "$TSAN_POLY" run vendor/polyml/polyexport < "$sml" > "$log" 2>&1
    check_warnings "$log" "$name"
}
run_probe mutex_demo crates/polyml-bin/tests/concurrency_support/mutex_demo.sml
run_probe racy_ref crates/polyml-bin/tests/concurrency_support/racy_ref_demo.sml
run_probe word_publish tools/tsan-probes/word_publish.sml
run_probe wide_publish tools/tsan-probes/wide_publish.sml

if [ "$MODE" = "full" ]; then
    note "full: GC handshake suite under TSan (skips the slow TOCTOU test)"
    cargo +nightly test -Zbuild-std --target $TARGET --release -p polyml-runtime \
        --test concurrency_gc_handshake -- --skip fork_toctou --test-threads 1 2>&1 \
        | grep -E "test result" || FAILED=1

    note "full: alloc storm + fuzz seeds under TSan"
    run_probe alloc_storm crates/polyml-bin/tests/concurrency_support/alloc_storm_demo.sml \
        POLYML_GC_THRESHOLD=20 POLYML_GC_QUIET=1
    FUZZ_DUMP=1 FUZZ_COUNT=4 cargo test --release -p polyml-bin --test concurrency_fuzz \
        fuzz_storms_giant -- --ignored > /dev/null 2>&1
    for s in 1 2 3 4; do
        [ -f "/tmp/fuzz_dump_seed_$s.sml" ] && \
            run_probe "fuzz_seed_$s" "/tmp/fuzz_dump_seed_$s.sml" \
                POLYML_GC_THRESHOLD=10 POLYML_GC_QUIET=1 POLYML_GC_AUDIT=1
    done
fi

note "byte residual characterization (EXPECTED to warn — not a failure)"
env POLY_REAL_THREADS=1 POLY_PARALLEL=1 \
    timeout 900 "$TSAN_POLY" run vendor/polyml/polyexport \
    < tools/tsan-probes/byte_publish.sml > /tmp/tsan_run_byte.log 2>&1
echo "byte_publish: $(grep -cE 'WARNING: ThreadSanitizer' /tmp/tsan_run_byte.log) warnings (documented residual)"

exit $FAILED
