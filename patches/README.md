# Vendored-compiler patches

`vendor/` is git-ignored, so changes to the vendored PolyML/Isabelle source can't
be committed directly. Patches that the build needs live here as tracked `.patch`
files and are applied idempotently by the build scripts.

- `tools/intflip-bootstrap.sh` applies `patches/polyml-*.patch` to `vendor/polyml`
  before the arbitrary-int self-bootstrap (baked into `/tmp/arbint_image`).
- `tools/isabelle-pure-probe.sh` applies `patches/isabelle-*.patch` to
  `vendor/isabelle/mirror-isabelle` before probing the Pure load (these are
  Isabelle *source* patches, applied at load time, not baked into the image).

Both skip patches already applied. To apply manually:

```sh
cd vendor/polyml && git apply ../../patches/polyml-<name>.patch
cd vendor/isabelle/mirror-isabelle && git apply ../../../patches/isabelle-<name>.patch
```

## Patches

- **polyml-isabelle-cartouche.patch** — `basis/String.sml`. Makes the compile-time
  string-literal converter (`convString`, installed via `RunCall.addOverload`) pass
  Isabelle symbol escapes `\<name>` / `\<^name>` through verbatim instead of raising
  "Invalid string constant". Isabelle source (e.g. `library.ML`) embeds these in
  string literals and is loaded by raw PolyML before `ml_lex.ML`, so the converter
  must accept them. Takes the Isabelle/Pure load from 27/282 → 102/282 files.
  See [[isabelle-go-signal]] in project memory.

- **isabelle-options-stub.patch** — `src/Pure/System/options.ML`. There is no
  Isabelle system process to supply `ISABELLE_PROCESS_OPTIONS`, so the bootstrap
  tail raised "Missing default for system options". Synthesise a default options
  table from the 14 options Pure declares at load (`Config.declare_option_*`,
  bool/int) and make `check_type` return a type-appropriate default for any other
  option read at load. Combined with loading via Isabelle's `ML_file` (which
  expands `\<^here>`), takes the Pure load 102/282 → 124/282; next wall is the
  Context machinery (`markup_kind.ML`: "Unknown context"). A source-only-load stub
  — option *values* are read at runtime, which we don't exercise yet.
