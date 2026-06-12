#!/usr/bin/env bash
# Build a WARM Isabelle/Pure checkpoint at /tmp/isabelle_pure (symlinked into the
# persistent store like the HOL4 checkpoints). Loads the source-loadable logical
# Pure (261/285 files: kernel + Isar + proof + method + simplifier + ...; the 24
# external/Scala/PIDE files are skipped) on the arbitrary-int image, then
# PolyML.export so downstream tests/agents start from a loaded Pure in seconds
# instead of recompiling 261 files (~5 min) each time.
#
# Prereqs: /tmp/arbint_image (tools/intflip-bootstrap.sh) + vendored Isabelle/Pure
# with patches applied (tools/isabelle-pure-probe.sh applies them idempotently).
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
POLY="$ROOT/target/release/poly"
IMG=/tmp/arbint_image
ISA="$ROOT/vendor/isabelle/mirror-isabelle"
PURE="$ISA/src/Pure"
OUT=/tmp/isabelle_pure
[ -f "$IMG" ] || { echo "missing $IMG — run tools/intflip-bootstrap.sh"; exit 1; }
[ -d "$PURE" ] || { echo "missing vendored Isabelle/Pure at $PURE"; exit 1; }

# Apply tracked Isabelle-source patches (vendor/isabelle is git-ignored).
for p in "$ROOT"/patches/isabelle-*.patch; do
    [ -f "$p" ] || continue
    if git -C "$ISA" apply --reverse --check "$p" >/dev/null 2>&1; then :
    elif git -C "$ISA" apply --check "$p" >/dev/null 2>&1; then
        git -C "$ISA" apply "$p" && echo "applied patch: $(basename "$p")"
    else echo "WARNING could not apply $(basename "$p")"; fi
done

# Build the ordered ML_file list (all ML_file* variants, ROOT0 then ROOT).
FILES=/tmp/pure_files.txt
{ grep -hoE 'ML_file[a-z_]* "[^"]+"' "$PURE/ROOT0.ML"; grep -hoE 'ML_file[a-z_]* "[^"]+"' "$PURE/ROOT.ML"; } \
    | sed -E 's/ML_file[a-z_]* "([^"]+)"/\1/' > "$FILES"

DRIVER=/tmp/build_isabelle_pure_driver.sml
{
  echo 'fun pr s = (print s; TextIO.flushOut TextIO.stdOut);'
  echo "val PURE = \"$PURE\";"
  echo 'val nok = ref 0; val idx = ref 0;'
  echo 'fun okf () = (idx := !idx+1; nok := !nok+1);'
  # per-statement, INLINE PolyML.use / ML_file (NOT wrapped in a function — a
  # function captures the ML environment at definition time and yields 204 not
  # 261; see isabelle-pure-probe.sh).
  awk 'NR<=27{printf "val () = (PolyML.use (PURE ^ \"/%s\"); okf ()) handle _ => ();\n", $0}' "$FILES"
  awk 'NR>27{printf "val () = (ML_file (PURE ^ \"/%s\"); okf ()) handle _ => ();\n", $0}' "$FILES"
  echo 'val () = pr ("ISABELLE_PURE_LOADED " ^ Int.toString (!nok) ^ "/" ^ Int.toString (!idx) ^ "\n");'
  # The generic context (proto-Pure theory + proof data) is thread-local and is
  # LOST when the image is reloaded into a fresh process ("Unknown context").
  # Capture it as an explicit heap binding `Pure_context` that survives export,
  # and a `restore_pure_context` thunk; reloaders call restore_pure_context ()
  # before any proving so Context.the_global_context()/Proof_Context.init_global
  # work again.
  echo 'val Pure_context = Context.the_generic_context ();'
  echo 'fun restore_pure_context () = Context.put_generic_context (SOME Pure_context);'
  # require the logical core (>= 255 of 285) before exporting a usable checkpoint
  cat <<SML
val () =
  if !nok >= 255 then
    (pr ("EXPORTING $OUT\n"); PolyML.export ("$OUT", PolyML.rootFunction);
     pr "ISABELLE_PURE_CHECKPOINT_DONE\n")
  else pr ("ISABELLE_PURE_EXPORT_SKIPPED (only " ^ Int.toString (!nok) ^ " loaded)\n");
SML
} > "$DRIVER"

echo "building Isabelle/Pure checkpoint -> $OUT (loading ~261 files, ~5 min) …"
( cd "$ROOT/vendor/polyml" && ML_SYSTEM=polyml ML_PLATFORM=x86_64-linux ISABELLE_HOME=/tmp/isa \
    POLYML_GC_QUIET=1 "$POLY" run --max-steps 300000000000 "$IMG" < "$DRIVER" ) 2>&1 \
  | grep -aE "ISABELLE_PURE_LOADED|EXPORTING|CHECKPOINT_DONE|EXPORT_SKIPPED"

if [ -f "$OUT" ]; then
  echo "isabelle-pure: OK ($(wc -c <"$OUT") bytes)"
  # relink into the persistent store if the relinker is present
  [ -x "$ROOT/tools/persist-ckpts.sh" ] && "$ROOT/tools/persist-ckpts.sh" >/dev/null 2>&1 || true
else
  echo "isabelle-pure: FAILED (no $OUT)"; exit 1
fi
