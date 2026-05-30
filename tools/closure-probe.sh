#!/usr/bin/env bash
# closure-probe.sh -- enumerate .sig/.sml under one or more HOL4 source dirs,
# generate a fixpoint-loader driver, and run it on a checkpoint via sml-exp.sh.
# Prints how many of that closure load (LOADED_OK n/m) + the stuck set +
# grouped diagnostics. A fast "how far does <subsystem> load?" probe.
#
# Usage: tools/closure-probe.sh <checkpoint> <reldir> [reldir...]
#   <checkpoint>  poly image (e.g. /tmp/hol4_theory)
#   <reldir>      dir under vendor/hol4 (e.g. src/parse) OR vendor/hol4-relative
# Env: POLY (default <repo>/target/release/poly)
set -uo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$SCRIPT_DIR/.." && pwd)"
H="$REPO/vendor/hol4"

CKPT="${1:-}"; shift || true
[ -z "$CKPT" ] || [ $# -eq 0 ] && { echo "usage: closure-probe.sh <checkpoint> <reldir>..." >&2; exit 2; }

DRV=/tmp/closure-probe.sml
{
  echo 'fun pr s = (print s; TextIO.flushOut TextIO.stdOut);'
  echo 'val HOL = "../hol4"; fun U f = PolyML.use (HOL ^ "/" ^ f);'
  echo 'structure PP = HOLPP;'
  echo 'val files = ['
  first=1
  for d in "$@"; do
    while IFS= read -r f; do
      rel="${f#"$H/"}"
      if [ $first -eq 1 ]; then first=0; else echo ','; fi
      printf '  "%s"' "$rel"
    done < <(find "$H/$d" -maxdepth 1 \( -name '*.sig' -o -name '*.sml' \) 2>/dev/null \
             | grep -vEi 'selftest|_test' | sort)
  done
  echo ''
  echo '];'
  cat <<'SML'
val errs = ref ([] : (string*string) list);
fun note (f,e) = errs := (f,e)::(List.filter (fn (g,_)=>g<>f) (!errs));
fun tryUse f = (U f; true) handle e => (note(f, exnMessage e); false);
fun pass (rem,prog) = case rem of [] => (prog,[])
  | f::rest => if tryUse f then let val (p,l)=pass(rest,true) in (p,l) end
               else let val (p,l)=pass(rest,prog) in (p,f::l) end;
fun loop (rem,n) = if n<=0 then rem else
  let val (_,left)=pass(rem,false) in
    if null left then [] else if length left=length rem then left else loop(left,n-1) end;
pr "CLOSURE_PROBE_START\n";
val stuck = loop (files, 12);
pr ("\nLOADED_OK " ^ Int.toString(length files - length stuck) ^ "/" ^ Int.toString(length files) ^ "\n");
pr ("STUCK_COUNT " ^ Int.toString(length stuck) ^ "\n");
List.app (fn f => pr ("STUCKERR " ^ f ^ "\n")) stuck;
pr "CLOSURE_PROBE_DONE\n";
SML
} > "$DRV"
echo "closure: $(grep -c '"' "$DRV") files from: $*"
"$SCRIPT_DIR/sml-exp.sh" "$CKPT" "$DRV"
