#!/usr/bin/env bash
# Tier B M2+M3: demonstrate a heap image built on x86_64 loading + executing
# on aarch64 — the "portable across arches" headline.
#
# Strategy: polyml-rs is an INTERPRETER, so our images are arch-neutral
# bytecode (no native code to relocate). At a fixed 64-bit word size an
# x86_64-produced pexport image is byte-for-byte loadable on aarch64. We build
# the `poly` binary for aarch64 with `cross` (a containerised cross toolchain +
# qemu-user) and run it under emulation on the same images we run on x86_64.
#
# Requirements: `cross` (cargo install cross) + docker or podman.
# See docs/tier-b-portable-images-design.md.
#
# Usage:
#   tools/cross-arch-demo.sh            # build aarch64 poly + run the demos
#   tools/cross-arch-demo.sh --build    # only cross-build the aarch64 binary
# Env:
#   CROSS_CONTAINER_ENGINE=podman   # if docker has no daemon (cross default is docker)
#   CROSS_CONTAINER_OPTS=-i         # set below: forwards host stdin into the
#                                   # container so M3b's piped REPL input reaches qemu
set -euo pipefail

cd "$(dirname "$0")/.."
TARGET=aarch64-unknown-linux-gnu
# `cross run` does NOT forward host stdin into the container by default, so a
# piped REPL (M3b: `echo … | cross run`) hits EOF and compiles nothing. Pass -i
# to the container engine so stdin is forwarded. (Caller-overridable.)
export CROSS_CONTAINER_OPTS="${CROSS_CONTAINER_OPTS:--i}"
BOOTSTRAP=vendor/polyml/bootstrap/bootstrap64.txt
POLYEXPORT=vendor/polyml/polyexport   # self-bootstrapped full image (optional)

step() { printf '\n\033[1;36m=== %s ===\033[0m\n' "$*"; }
die()  { printf '\033[1;31mFAIL: %s\033[0m\n' "$*" >&2; exit 1; }

command -v cross >/dev/null || die "cross not found (cargo install cross); needs docker/podman"

step "Cross-building poly for $TARGET (Cranelift is pure-Rust → cross-compiles)"
# If Cranelift/JIT fails to cross-compile, the fallback is to feature-gate the
# JIT out of polyml-bin (interpreter-only) — see the design doc. Try the full
# build first; it is expected to work.
cross build --release --target "$TARGET" -p polyml-bin \
    || die "aarch64 build failed — consider feature-gating the JIT (design doc M2)"

BIN="target/$TARGET/release/poly"
[ -f "$BIN" ] || die "expected binary $BIN not produced"
step "Built $BIN"
file "$BIN" 2>/dev/null | sed 's/^/  /' || true

if [ "${1:-}" = "--build" ]; then exit 0; fi

# --- M3a: load + execute a checked-in image on aarch64 (proves portability) ---
step "M3a: run the simple bootstrap on aarch64 (under qemu via cross)"
[ -f "$BOOTSTRAP" ] || die "missing $BOOTSTRAP"
OUT=$(cross run --release --target "$TARGET" -p polyml-bin -- run "$BOOTSTRAP" 2>&1) \
    || { echo "$OUT"; die "aarch64 bootstrap run errored"; }
echo "$OUT" | tail -4 | sed 's/^/  /'
echo "$OUT" | grep -q "Tagged(0) — clean return" \
    || die "aarch64 bootstrap did not return Tagged(0)"
step "M3a PASS — x86_64-checked-in bytecode image executed on aarch64"

# --- M3b: the REPL headline, if a self-bootstrapped full image exists ---
if [ -f "$POLYEXPORT" ]; then
    step "M3b: run 'fact 10' through the self-bootstrapped image on aarch64"
    PROG='fun fact 0 = 1 | fact n = n * fact(n-1); fact 10;'
    OUT=$(echo "$PROG" | cross run --release --target "$TARGET" -p polyml-bin \
            -- run --max-steps 500000000 "$POLYEXPORT" 2>&1) \
        || { echo "$OUT"; die "aarch64 polyexport REPL errored"; }
    echo "$OUT" | grep -E 'val it|3628800' | sed 's/^/  /' || true
    echo "$OUT" | grep -q "3628800" \
        || die "aarch64 REPL did not compute fact 10 = 3628800"
    step "M3b PASS — an image our x86_64 runtime self-bootstrapped ran a real SML REPL on aarch64"
else
    step "M3b SKIP — $POLYEXPORT not present (run the Stage1 chain to produce it first)"
fi

step "Cross-arch demo complete"
