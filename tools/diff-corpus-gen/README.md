# diff-corpus-gen — type-directed random SML program fuzzer

This directory holds **whole-program** generators for the differential
faithfulness oracle. Each generator emits a batch of self-contained,
**well-typed-by-construction**, **deterministic** SML programs. Every program
prints exactly one `@@<label>=<value>` line; `tools/diff-oracle.sh` runs it
through OURS (`poly run <checkpoint>`) and the trusted upstream `poly` and
compares that line byte-for-byte. Any difference is a faithfulness bug in OUR
port (compiler-execution + interpreter + RTS + GC), never a test artifact.

## Why whole programs (vs the per-op `fuzz_*.sml`)

The per-op fuzzers (`tools/diff-corpus/fuzz_{int,word,real,list,string,...}.sml`)
exercise ONE operation at a time. These generators build **whole programs** —
novel control flow + FEATURE COMBINATIONS (nested `let`, `if`/`case` dispatch,
recursion via fuel'd helpers, list/HOF pipelines, exception flow, user datatypes,
allocation/GC pressure). A bug that only fires in a *combination* (cf. the
`PolySubtractArbitrary` RTS-path bug invisible to the opcode-path corpus) is the
target.

## Soundness invariants (shared by every generator)

1. **Type-directed** → well-typed by construction. `gen(ty,...)` only ever emits
   an expression of exactly `ty`. No type errors ⇒ both sides compile + run ⇒
   any `@@` divergence is a genuine OUR-side bug.
2. **Deterministic LCG** (MMIX constants, same PRNG as `fuzz_*.sml`) → same seed
   ⇒ byte-identical program files. The generated programs are themselves
   deterministic (no input, no clock, no run-time randomness).
3. **Every result wrapped** → an exception becomes a comparable token
   (`OVF`/`DIV`/`SUB`/`USR1`/…). Both sides raising the same exn ⇒ they agree.
4. **Bounded** → expression depth, list lengths, tabulate/alloc counts, tree
   depth, recursion fuel all capped ⇒ programs terminate fast and stay small.
5. **Totally stringified, deterministic output** → `Int.toString`/`Bool.toString`
   + fixed list/pair stringifiers. NO `Real` formatting, NO ref/exn/function
   *printing*, NO `andb`/`orb` on big `IntInf` (the known stage-0 quirk).

## The generators (one per FEATURE DIMENSION)

| file | dimension | what it stresses |
|------|-----------|------------------|
| `genprog.sml` | (shared core / base) | the framework: typed env, LCG, productions |
| `genprog_arith.sml` | **arith_control** | deeply nested int/IntInf/word arithmetic + if/case control flow |
| `genprog_lists_hof.sml` | **lists_hof** | lists + tuples + higher-order fns (map/fold/filter/partition/tabulate/find/…) |
| `genprog_dre.sml` | **datatypes_rec_exn** | user datatypes (tree/option/either) + recursion + exception flow |
| `genprog_strings_closures.sml` | **strings_closures** | string ops + captured-variable closures passed to HOFs |
| `genprog_gc_pressure.sml` | **gc_pressure** | alloc-heavy programs: big tabulate/lists/refs/trees, alloc storms, deep pointer chains the GC must walk |

## Reproducible workflow

Generation runs on the trusted UPSTREAM poly. All env vars read via
`OS.Process.getEnv`:

```
GENPROG_SEED   (default 1)            -- LCG seed; change => a different batch
GENPROG_N      (default 30)           -- number of program files to emit
GENPROG_OUT    (default /tmp/genprog) -- output directory (created if absent)
GENPROG_DEPTH  (default 5)            -- max expression depth
GENPROG_PREFIX (default p)            -- file/label prefix: <PREFIX><i>.sml
```

The exact recipe that produced the banked corpus (seed 42; counts matching the
fan-out: arith/lists/dre/strings = 600, gc = 400):

```sh
UP=/tmp/polybuild/poly      # trusted upstream oracle (tools/build-oracle.sh)
gen() {  # file out n prefix
  rm -rf "tools/diff-corpus-gen/out/$2"; mkdir -p "tools/diff-corpus-gen/out/$2"
  GENPROG_SEED=42 GENPROG_N=$3 GENPROG_OUT="tools/diff-corpus-gen/out/$2" \
    GENPROG_PREFIX="$4" "$UP" < "tools/diff-corpus-gen/$1"
}
gen genprog_arith.sml            arith_control     600 genprog_arith_
gen genprog_lists_hof.sml        lists_hof         600 genprog_lists_hof_
gen genprog_dre.sml              datatypes_rec_exn 600 genprog_dre_
gen genprog_strings_closures.sml strings_closures  600 genprog_sc_
gen genprog_gc_pressure.sml      gc_pressure       400 genprog_gc_pressure_
```

`out/` is git-ignored (it is fully reproducible from the recipe above). Verify a
batch:

```sh
tools/diff-oracle.sh --dir tools/diff-corpus-gen/out/<dim>                       # vs native
POLY_UPSTREAM=/tmp/polybuild-interp/poly tools/diff-oracle.sh --dir <as above>   # vs bytecode-interp
```

## What is BANKED (tracked in git)

- **The generators themselves** (`tools/diff-corpus-gen/*.sml`) — so the full
  batches can be regenerated/expanded at will.
- **A frozen, vetted regression subset** under
  `tools/diff-corpus/genprog/<dim>/` (300 programs, 60 per dimension) — small
  enough that `tools/diff-oracle.sh --dir tools/diff-corpus` (wired into
  `tools/regression.sh full`) stays fast, while still exercising every
  dimension. See `tools/diff-corpus/genprog/README.md`.

## Last full sweep (2026-06-17)

Seed 42, 2800 programs (600/600/600/600/400). **All 2800 byte-identical to the
upstream native oracle; all 2800 byte-identical to the upstream bytecode-interp
oracle.** Zero divergences, zero OUR-side bugs found. The frozen 300 are a
representative slice of that clean set.
