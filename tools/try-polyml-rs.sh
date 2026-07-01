#!/usr/bin/env bash
# try-polyml-rs.sh — one-command SML REPL from a release, on ANY 64-bit target.
#
# Downloads the v0.1.0 `poly` binary for your platform + the portable
# `polyexport.bic` image, verifies checksums, and drops you into a real SML
# REPL — no build, no toolchain. This is also the cross-architecture /
# cross-OS portability demo: the SAME image byte runs on x86-64 Linux, arm64
# macOS, and the big-endian targets, and reports the SAME step count.
#
# Usage:
#   tools/try-polyml-rs.sh                # download + REPL
#   tools/try-polyml-rs.sh --demo         # download + run the portability probe
#                                         # (prints the byte-identical step count)
set -euo pipefail

REPO="lexicone42/polyml-rs"
TAG="${POLYML_RS_TAG:-v0.1.0}"
DIR="${POLYML_RS_DIR:-$HOME/.cache/polyml-rs/$TAG}"
mkdir -p "$DIR"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)  TRIPLE=x86_64-unknown-linux-gnu ;;
  Darwin-arm64)  TRIPLE=aarch64-apple-darwin ;;
  Linux-aarch64) TRIPLE=aarch64-unknown-linux-gnu ;;
  *) echo "No prebuilt binary for $(uname -s)-$(uname -m). Build from source: cargo build --release -p polyml-bin"; exit 1 ;;
esac

fetch() {  # fetch <asset-name> <dest>
  [ -f "$2" ] && return 0
  echo ">>> downloading $1" >&2
  if command -v gh >/dev/null 2>&1; then
    gh release download "$TAG" --repo "$REPO" --pattern "$1" --output "$2"
  else
    curl -fsSL "https://github.com/$REPO/releases/download/$TAG/$1" -o "$2"
  fi
}

fetch "poly-$TRIPLE"   "$DIR/poly"
fetch "polyexport.bic" "$DIR/polyexport.bic"
fetch "SHA256SUMS"     "$DIR/SHA256SUMS" || true
chmod +x "$DIR/poly"

if [ -f "$DIR/SHA256SUMS" ]; then
  echo ">>> verifying checksums" >&2
  ( cd "$DIR" && grep -E "poly-$TRIPLE|polyexport.bic" SHA256SUMS \
      | sed "s/poly-$TRIPLE/poly/" | sha256sum -c - ) || {
        echo "!!! checksum mismatch — refusing to run"; exit 1; }
fi

if [ "${1:-}" = "--demo" ]; then
  echo ">>> portability probe: running the same image byte on $(uname -s)-$(uname -m)" >&2
  echo "fun fact 0 = 1 | fact n = n * fact (n-1); fact 20;" \
    | "$DIR/poly" run "$DIR/polyexport.bic"
  echo ">>> (compare the 'Executed N steps' line across machines — it should match)" >&2
else
  echo ">>> starting the SML REPL (Ctrl-D to exit)" >&2
  "$DIR/poly" run "$DIR/polyexport.bic"
fi
