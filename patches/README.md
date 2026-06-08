# Vendored-compiler patches

`vendor/` is git-ignored, so changes to the vendored PolyML/Isabelle source can't
be committed directly. Patches that the build needs live here as tracked `.patch`
files and are applied idempotently by the build scripts.

`tools/intflip-bootstrap.sh` applies every `patches/*.patch` to `vendor/polyml`
(via `git apply`, skipping any already applied) before running the arbitrary-int
self-bootstrap. To apply manually:

```sh
cd vendor/polyml && git apply ../../patches/<name>.patch
```

## Patches

- **polyml-isabelle-cartouche.patch** — `basis/String.sml`. Makes the compile-time
  string-literal converter (`convString`, installed via `RunCall.addOverload`) pass
  Isabelle symbol escapes `\<name>` / `\<^name>` through verbatim instead of raising
  "Invalid string constant". Isabelle source (e.g. `library.ML`) embeds these in
  string literals and is loaded by raw PolyML before `ml_lex.ML`, so the converter
  must accept them. Takes the Isabelle/Pure load from 27/282 → 102/282 files.
  See [[isabelle-go-signal]] in project memory.
