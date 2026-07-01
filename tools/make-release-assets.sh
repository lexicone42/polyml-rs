#!/usr/bin/env bash
# make-release-assets.sh — build the downloadable v0.1.0 release assets.
#
# Produces, under dist/:
#   poly-<triple>            the release `poly` binary for the host
#   polyexport.bic           the self-bootstrapped SML REPL image, in the
#                            compact binary bicimage format (~½ the pexport size,
#                            endian-neutral on the wire)
#   SHA256SUMS               checksums of the above
#
# The bicimage is DERIVED from the upstream LGPL-2.1 basis (see NOTICE below and
# docs/REPRODUCING.md); it is a release *asset*, never committed to this repo.
#
# Prerequisites: a self-bootstrapped vendor/polyml/polyexport (README example #2,
# ~5 min) and `cargo build --release`.
set -euo pipefail
cd "$(dirname "$0")/.."

TRIPLE="$(rustc -vV | sed -n 's/host: //p')"
OUT="dist"
mkdir -p "$OUT"

echo ">>> building release poly ($TRIPLE)"
cargo build --release -p polyml-bin
cp target/release/poly "$OUT/poly-$TRIPLE"

if [ ! -f vendor/polyml/polyexport ]; then
  echo "!!! vendor/polyml/polyexport missing — build it first (README example #2):"
  echo "    cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \\"
  echo "        bootstrap/bootstrap64.txt < bootstrap/Stage1.sml"
  exit 1
fi

echo ">>> converting polyexport -> bicimage"
target/release/poly bic vendor/polyml/polyexport "$OUT/polyexport.bic"

echo ">>> smoke-testing the asset (fact 10 == 3628800)"
out=$(echo "fun fact 0 = 1 | fact n = n * fact (n-1); fact 10;" \
      | "$OUT/poly-$TRIPLE" run "$OUT/polyexport.bic")
echo "$out" | grep -q 3628800 || { echo "!!! asset smoke test FAILED"; exit 1; }

echo ">>> checksums"
( cd "$OUT" && sha256sum "poly-$TRIPLE" polyexport.bic > SHA256SUMS && cat SHA256SUMS )

cat <<EOF

Assets ready in $OUT/. To publish a GitHub release:
    gh release create v0.1.0 --title "polyml-rs v0.1.0" --notes-file docs/RELEASE-NOTES.md \\
        "$OUT/poly-$TRIPLE" "$OUT/polyexport.bic" "$OUT/SHA256SUMS"
(Attach binaries for other targets from the nightly cross/macos jobs' artifacts.)

NOTICE: polyexport.bic embeds compiled code derived from the upstream Poly/ML
basis library (LGPL-2.1). Distribute the release with that attribution and a
pointer to https://github.com/polyml/polyml — see docs/REPRODUCING.md.
EOF
