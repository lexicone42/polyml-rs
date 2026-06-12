#!/usr/bin/env bash
# Measure how far Isabelle/Pure loads on the arbitrary-precision-int image.
#
# Loads the full ROOT0+ROOT ML_file sequence on /tmp/arbint_image: Phase 0 (the
# first 27 files) via raw PolyML.use to bring up ml_compiler0, then the rest via
# Isabelle's own `ML_file` (which expands `\<^here>` and other bootstrap
# antiquotations via ml_input). Reports "PURE_LOADED n/m first_fail=..." plus each
# failing file, so the next wall is obvious.
#
# Prereqs: /tmp/arbint_image (tools/intflip-bootstrap.sh) + vendored Isabelle/Pure.
# Applies tracked Isabelle-source patches (patches/isabelle-*.patch) idempotently.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
POLY="$ROOT/target/release/poly"
IMG=/tmp/arbint_image
ISA="$ROOT/vendor/isabelle/mirror-isabelle"
PURE="$ISA/src/Pure"
[ -f "$IMG" ] || { echo "missing $IMG — run tools/intflip-bootstrap.sh"; exit 1; }
[ -d "$PURE" ] || { echo "missing vendored Isabelle/Pure at $PURE"; exit 1; }

# Apply tracked Isabelle-source patches (vendor/isabelle is git-ignored).
for p in "$ROOT"/patches/isabelle-*.patch; do
    [ -f "$p" ] || continue
    if git -C "$ISA" apply --reverse --check "$p" >/dev/null 2>&1; then
        echo "probe: patch already applied: $(basename "$p")"
    elif git -C "$ISA" apply --check "$p" >/dev/null 2>&1; then
        git -C "$ISA" apply "$p" && echo "probe: applied patch: $(basename "$p")"
    else
        echo "probe: WARNING could not apply $(basename "$p")"
    fi
done

# Build the ordered ML_file list (ROOT0 then ROOT). NB: match ALL ML_file*
# variants in order — ROOT.ML loads 3 files via `ML_file_no_debug`
# (ML/exn_debugger.ML, Isar/runtime.ML, Tools/debugger.ML). Matching only the
# plain `ML_file "..."` silently DROPPED those, so Isar/runtime.ML never loaded
# and PIDE/execution.ML (which needs `Runtime`) failed — making the load look
# walled at #160 when it actually reaches #191 (ml_antiquotations.ML).
FILES=/tmp/pure_files.txt
{ grep -hoE 'ML_file[a-z_]* "[^"]+"' "$PURE/ROOT0.ML"; grep -hoE 'ML_file[a-z_]* "[^"]+"' "$PURE/ROOT.ML"; } \
    | sed -E 's/ML_file[a-z_]* "([^"]+)"/\1/' > "$FILES"

DRIVER=/tmp/pure_probe_driver.sml
{
  echo 'fun pr s = (print s; TextIO.flushOut TextIO.stdOut);'
  echo "val PURE = \"$PURE\";"
  echo 'val nok = ref 0; val idx = ref 0; val firstfail = ref "";'
  echo 'fun okf () = (idx := !idx+1; nok := !nok+1);'
  echo 'fun failf f = (idx := !idx+1; (if !firstfail="" then firstfail := (Int.toString(!idx)^":"^f) else ()); pr ("ISA_FAIL #"^Int.toString(!idx)^" "^f^"\n"));'
  # Load each file as its OWN top-level statement, with the PolyML.use / ML_file
  # call INLINE (not wrapped in a function). Two reasons:
  #  (1) per-statement: antiquotation-handler registrations (add_antiquotation in
  #      ml_antiquotations.ML etc.) only commit to the generic context at a
  #      top-level statement boundary, so a single List.app over the whole list
  #      starves later files' @{...} expansions.
  #  (2) INLINE: an `fun useM f = ML_file ...` captures the ML compilation
  #      environment at its DEFINITION time, so every later file would compile
  #      against a stale namespace (gives 204, not 261). Inlining each ML_file at
  #      top level uses the current accumulated environment.
  # Phase 0 (first 27) via PolyML.use bring up ml_compiler0, which DEFINES ML_file.
  awk 'NR<=27{printf "val () = (PolyML.use (PURE ^ \"/%s\"); okf ()) handle _ => failf \"%s\";\n", $0, $0}' "$FILES"
  awk 'NR>27{printf "val () = (ML_file (PURE ^ \"/%s\"); okf ()) handle _ => failf \"%s\";\n", $0, $0}' "$FILES"
  echo 'val () = pr ("PURE_LOADED " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!idx) ^ " first_fail=" ^ !firstfail ^ "\n");'
  echo 'pr "PURE_PROBE_DONE\n";'
} > "$DRIVER"

cd "$ROOT/vendor/polyml" || exit 1
ML_SYSTEM=polyml ML_PLATFORM=x86_64-linux ISABELLE_HOME=/tmp/isa POLYML_GC_QUIET=1 \
    "$POLY" run --max-steps 250000000000 "$IMG" < "$DRIVER" 2>&1 \
    | grep -E "ISA_FAIL|PURE_LOADED|PURE_PROBE_DONE"
