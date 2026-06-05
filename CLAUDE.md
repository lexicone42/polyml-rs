# polyml-rs — notes for future participants

## What this is

A Rust rewrite of PolyML's bytecode interpreter, runtime, and image
loader. Goal: faithful port of upstream's `vendor/polyml/libpolyml/`
semantics with stronger memory safety and a friendlier development
loop. See `PLAN.md` for the staged roadmap.

## Demo (Monday)

Five things to show:

### 1. `poly run` executes the real PolyML bootstrap image

```
$ cargo build --release -p polyml-bin
$ ./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt
Loaded vendor/polyml/bootstrap/bootstrap64.txt
  RTS patch: 39 resolved, 0 unresolved
Executing (cap 5000000 steps)…
Executed 1111155 bytecode step(s).
Result: Tagged(0) — clean return
```

### 2. The bootstrap is a real SML compiler

```
$ echo "1+1;" | ./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt
Error- in '<stdin>', line 1.
Type error in function application. Function: 1 : int ...
```

That error message is being emitted by the PolyML compiler running
in our Rust interpreter, formatted and written through our stdio
subcode-11/12 path. Real ML compiler output.

### 3. The full bootstrap chain runs through our runtime

```
$ cd vendor/polyml/
$ ../../target/release/poly run --max-steps 2000000000000 bootstrap/bootstrap64.txt < bootstrap/Stage1.sml
... basis loads ...
******Bootstrap stage 2 of 7******
Making MLCompiler
... ~150 modules compiled ...
Created structure MLCompiler
******Bootstrap stage 3 of 7******
... basis re-loads on the freshly-compiled compiler ...
******Bootstrap stage 4 of 7******
... PolyML.make MLCompiler again ...
******Bootstrap stage 5 of 7******
******Bootstrap stage 6 of 7******
******Bootstrap stage 7 of 7******
******Writing object code******
Result: Tagged(0) — clean return
```

Every stage of PolyML's self-compilation chain runs end-to-end
through our Rust interpreter — same source the upstream PolyML
build uses to bootstrap itself.

Stage 7's `PolyML.export(fileName, root)` is wired up to
[`polyml_runtime::export::snapshot`] + [`Image::write`] and writes
a real pexport text file. **The full bootstrap loop closes
end-to-end into a working SML REPL:**

```
$ cd vendor/polyml/
$ ../../target/release/poly run --max-steps 200000000000 \
      bootstrap/bootstrap64.txt < bootstrap/Stage1.sml
# ... ~5 minutes of self-compilation ...
******Writing object code******
Result: Tagged(0) — clean return

$ ls -l polyexport
-rw-r--r-- 13248269  (13 MB, 453K objects)

$ echo "fun fact 0 = 1 | fact n = n * fact(n-1); fact 10;" \
    | ../../target/release/poly run --max-steps 500000000 polyexport
Poly/ML 5.9.2 Release (Git version polyml-rs)
> val fact = fn: int -> int
> val it = 3628800: int
Result: Tagged(0) — clean return
```

That's a real SML REPL — type inference, recursive functions,
higher-order functions, lists — running an image our Rust runtime
self-bootstrapped from `bootstrap64.txt`. The simpler "load only,
trivial root" form also works:

```
$ cat > /tmp/quick.sml <<'EOF'
val () = Bootstrap.use "basis/build.sml";
val () = PolyML.export("/tmp/my_export", fn () => ());
EOF
$ cd vendor/polyml
$ ../../target/release/poly run bootstrap/bootstrap64.txt < /tmp/quick.sml
$ ../../target/release/poly run /tmp/my_export
# starts executing the re-loaded image
```

`PolyML.shareCommonData` is still a no-op (deduplication-style
optimization; safe to skip).

Heap default is 1.6 GB (200M words × 8 bytes; `with_default_alloc_space`
takes a *word* count — easy footgun). At that size the Cheney copying
GC fires regularly (~18 cycles over the 7-stage chain, each retaining
10-15M live words out of 167M), keeping peak RSS around 1.6 GB and
letting the whole chain complete in ~5 minutes on a 6-core machine.
A much larger heap (e.g. 24 GB) postpones GC past the bootstrap's
working set, the chain accumulates without compaction, and the OOM
killer takes the process out around stage 6 on a 32 GB machine.
Useful env vars: `POLYML_GC_THRESHOLD` overrides the 80% trigger;
`POLYML_GC_QUIET=1` silences per-cycle log; `POLYML_GC_AUDIT=1`
checks for residual from-space pointers across interpreter state
after each collect (slow — debugging aid).

### 4. Run an SML file as a one-shot script

`poly run --use file.sml` is the simplest "run this program" surface:

```
$ cat > /tmp/script.sml <<'EOF'
infix 6 +;
RunCall.addOverload FixedInt.+ "+";
val answer = 21 + 21;
EOF
$ ./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt \
                              --use /tmp/script.sml
Use: script.sml
Result: Tagged(0) — clean return
```

Internally: the CLI synthesizes `val () = Bootstrap.use "script.sml";`
to stdin, sets `CommandLine.arguments` to `["-I", "/tmp"]`, then
redirects real stdin from `/dev/null` so the bootstrap REPL exits
on EOF after the synthetic line is consumed. `PolyBasicIOGeneral`
subcodes 3/4/8/9 do the actual file open + read.

For more control, the long form is:

```
$ echo 'val () = Bootstrap.use "script.sml";' \
    | ./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt \
                                -- -I /tmp
```

The `-- ARGS` after the image populates `CommandLine.arguments()`
for the SML side; useful for any SML program that scans args.

### 5. HOL4 theorem-proving runs through our runtime

```
$ cargo test --release -p polyml-bin --test hol4_recon \
    recon_via_checkpoint_proves_implication_self -- --nocapture
... 15 seconds ...
test recon_via_checkpoint_proves_implication_self ... ok
```

The test loads HOL4's kernel (Type, Term, Subst, Net, Thm) through
`PolyML.use` into a basis-loaded checkpoint, then constructs and
verifies 12 primitive HOL4 inferences (REFL, ASSUME, DISCH, MP,
TRANS, SYM, EQ_MP, AP_TERM, BETA_CONV, ABS, MK_COMB, INST_TYPE) plus
two derived theorems (transitivity of `==>`, Leibniz substitution).
Every theorem object is constructed by HOL4's actual LCF-style
kernel running on our Rust interpreter — not a simulation.

The strict test (`assert_compile_clean` in `hol4_recon.rs`) rejects
any `: error:` or `Static Errors` output during the load chain, so
silent compile failures can't sneak past.

## Bootstrap image structure (important!)

`vendor/polyml/bootstrap/bootstrap64.txt` is **Stage 0** — the bare
PolyML compiler with NO basis loaded. It's designed to be driven by
piping `bootstrap/Stage1.sml` to stdin with `-I <srcdir>` so it can
locate basis source files. The build command:

```
./polyimport bootstrap/bootstrap64.txt -I . < bootstrap/Stage1.sml
```

Consequences for testing:
- `1 + 1;` produces a type error — `+` exists as an overloaded
  identifier but no concrete overload is registered.
- Infix declarations (`infix 6 +`) and operator overloads
  (`RunCall.addOverload FixedInt.+ "+"`) are NOT in scope at the
  initial REPL. The first lines of `basis/InitialBasis.ML` install
  them.
- For minimal arithmetic without loading basis files, prepend the
  necessary declarations:
  ```sml
  infix 6 + -;
  RunCall.addOverload FixedInt.+ "+";
  val x = 1 + 2;  (* now succeeds *)
  ```

The `bootstrap_can_register_infix_plus_and_compute` test in
`crates/polyml-bin/tests/cli_run.rs` exercises this path.

## Performance

The bytecode interpreter dispatch loop went through ~8x of perf
work in May 2026. Current state (5.9 GHz Intel, single core):

| Workload                              | Time   | Steps    | Steps/sec |
|---------------------------------------|--------|----------|-----------|
| Simple bootstrap (no stage1)          | 0.1s   | 1.1M     | 11M       |
| Basis load (`Bootstrap.use "basis/build.sml"`) | 20s | 1.8B | 90M |
| Full 7-stage chain                    | 5min   | 27.7B    | 92M       |
| HOL4 kernel + 14 inferences proof     | 15s    | ?        | ?         |

Two structural fixes account for most of the gain:
1. `gc_threshold_percent()` cached in `AtomicUsize` — was reading
   env var on every step → 6.2x.
2. Pre-computed `gc_trigger_words` from `cap * threshold / 100`,
   plus `#[inline(always)]` + `get_unchecked` on push/pop/peek/
   reset/drop_n → 1.35x more.

Use `poly run --profile <image>` to dump hot opcodes / hot code
objects. Top-20 hottest opcodes is invaluable for finding the next
target — the env-var-cache fix came from "wait, LOCAL_N is 17%
combined; what's actually slow in that path?"

Next-hottest opcodes (post-fix) are INDIRECT_LOCAL_B0/B1 (~7%)
and the JUMP family (~6%). Diminishing returns — each is already
~3 instructions of useful work.

## JIT status — runs the full pipeline end-to-end

`poly run --jit image.txt` installs JIT-translatable code objects
whose opcodes we trust, then dispatches via the JIT cache. Verified
end-to-end:
- Simple bootstrap (1,110,404 steps, Tagged(0))
- Full Stage1 7-stage chain (27,676,346,761 steps, Tagged(0), writes
  polyexport)
- Re-loading the JIT-built polyexport: works as a real SML REPL
  (`fact 10` returns `3628800: int`)
- All 6 HOL4 tests pass with JIT enabled (kernel construction,
  primitive inference rules, derived theorems)

**Current coverage** (2026-05-28): 3,265 / 4,436 code objects
translate (73.6%), 592 install (the install filter rejects functions
whose bytecode contains opcodes whose translations we don't yet
trust). The big jump from 60% → 73% happened on 2026-05-28 by
implementing STACK_CONTAINER_B (+122), LOCK/CLEAR_MUTABLE (+170),
BLOCK_EQUAL_BYTE (+65), GET_THREAD_ID (+16), and a handful of
smaller opcodes.

The opcodes we currently SKIP at install time (`install_all_jit_entries`
in `polyml-jit/src/lib.rs`):
- CALL_LOCAL_B (0x16), TAIL_B_B (0x7b) — peek-don't-pop calling
  conventions our trampoline path doesn't fully model.
- CALL_CONST_ADDR variants (0x57/0x58/0x17/0x18) — translation
  loads closure pointer at runtime, but the call still SEGVs
  downstream in unisolated cases.

Top remaining translation blockers (= functions that don't even
translate, much less install):
- CALL_CLOSURE (0x0c, 268 functions) — needs runtime arity discovery
- ESCAPE (0xfe, 129 functions) — gateway to 77 extended opcodes
- BLOCK_COMPARE_BYTE (0xee, 5) — like BLOCK_EQUAL_BYTE but tri-valued
- LDEXC (0x6d, 11) — load current exception, needs handler state
- ALLOC_MUT_CLOSURE_B (0x76, 10) — mutable closure alloc

Now SAFE (re-enabled, no regressions):
- RAISE_EX (0x10), SET_HANDLER8/16 (0x81/0xf9), CLOSURE_B (0xd0),
  ALLOC_REF/BYTE_MEM/WORD_MEM (0x06/0xbd/0xda)
- CONST_ADDR (load) variants 0x55/0x56/0x15/0x14
- CASE16 (0x0a) — translation added (jump table → Cranelift
  br_table), 4 new functions translate; some still fail with
  `Underflow` (downstream depth tracking through CASE16 branches
  needs more work).
- Functions where `jit_arity_init > sml_arity + 2` — args_buf
  layout fix in do_call handles older-slot positions correctly.

## JIT execution profile

`poly run --jit --profile <image>` adds:
- Per-function JIT cache hit count
- Identifies hottest un-JIT'd functions
- Names the likely blocker opcode for each

On the simple bootstrap: only 3.8% of all CALL dispatches hit the
JIT cache. The hot path is mostly in functions filtered by
CALL_LOCAL_B (2 of top 10), CASE16 (3), CALL_CONST_ADDR (1),
TAIL_B_B (1), STACK_CONTAINER_B (1). Fixing those is the next
real perf lever.

Bisection harness env vars (in `install_all_jit_entries`):
- `JIT_INSTALL_LIMIT=N` — install only the first N entries.
- `JIT_INSTALL_SKIP=N,M,K` — skip specific install indices.
- `JIT_INSTALL_VERBOSE=1` — print every install line.
- `JIT_INSTALL_DUMP_IDX=N` — dump bytecode of install index N.

The fixes that unlocked this (commit `598f312` after `1d2c524` and
`e6a8280`):
1. `do_call`'s args_buf layout populates older-slot positions when
   arity_init > sml_arity + 2 (matches SML stack semantics).
2. `closure_call_trampoline` reverses args (same pattern as
   `rts_trampoline`) so `args[0]` = SML's arg_0 = deepest pushed.
3. Install filter skips functions whose JIT translation we don't
   yet trust.

Next steps to bring installed count back up:
1. Diagnose the CONST_ADDR translation. Bisection (commit `598f312`
   message) suggests stale baked addresses after GC. Fix it and
   re-enable those opcodes.
2. Build a differential tester (run a single function in both JIT
   and interp, compare results) to find further bugs systematically.
3. Tackle the CALL_LOCAL_B / TAIL_B_B / exception classes.

Diagnostic env vars added during this work:
- `POLY_CHECKPOINT_EVERY=N` — main loop prints step count every N.
- `JIT_TRACE_RETURNS=1` — `do_return` dumps frame on bad retPC.
- `JIT_TRAMP_DUMP_ARGS=1` — `closure_call_trampoline` logs raw args.
- `JIT_TRAMP_STEP_TRACE=1` (+ optional `JIT_TRAMP_STEP_ALL=1`) —
  per-step trace inside trampoline runs.
- `JIT_TRACE_CALLS_BC=1` — extend JIT call trace with bytecode head.
- `JIT_TRAMP_PANIC_ON_ERR=1` — abort on trampoline error.
- `JIT_TRACE_STORES=1` — `STORE_ML_WORD` dumps on suspicious base.



The JIT translates bytecode to Cranelift IR. ~60% of real bootstrap
code objects compile cleanly. Coverage report via:

    cargo test --release -p polyml-jit --test coverage_bootstrap -- --nocapture

**Three breakthroughs landed today** (commits af7c578, 9c43ee5, 3c5197b):

1. **arity mismatch** (af7c578): `infer_arg_count` used the JIT's
   depth-from-stack-top model, but SML's call frame is
   `[arg, retPC, closure]` (3 slots). Functions with
   `INDIRECT_CLOSURE_B0 depth=1` read the wrong slot. Fixed by
   taking `max(infer, sml_arity + 2)` as JIT-internal arg_count.

2. **CLOSURE_B order** (9c43ee5): JIT was popping src closure
   FIRST then captures. Upstream `CREATE_CLOSURE` pops captures
   first (top → slot N), then peeks src. Swap fixed.

3. **JIT-↔-interp recursion** (3c5197b): nested JIT calls inside
   JIT'd code (via the trampoline) added Rust call frames. Deeply
   recursive bootstrap code (entry [52] + its mutually-recursive
   callees) blew the 8 MB OS thread stack. Gated nested fast paths
   on `JIT_INTERP` / `JIT_DEPTH` so recursion stays on the
   interpreter's managed PolyWord stack.

Verification via the bisection harness:

    JIT_BOOTSTRAP_INSTALL=N cargo test --release -p polyml-jit --test jit_bootstrap_run

Installing ALL 2094 JIT entries runs the simple bootstrap cleanly
in 1,111,155 steps (Tagged(0)). Pre-session: install=24 SEGV'd
immediately. Today's three fixes unlocked the entire JIT path.

**Caveats:**
- Only the OUTERMOST JIT dispatch (from interpreter's CALL opcode
  into a JIT-cached function) takes the fast path. Nested calls
  fall through to the interpreter. Bumping `MAX_JIT_DEPTH > 0` in
  `jit_bridge.rs` re-enables nested JIT-to-JIT, but there's a
  separate SEGV bug in that path (visible at install=53 with
  MAX_JIT_DEPTH=4096) that needs diagnosing first.
- The full 7-stage chain isn't yet exercised with JIT installs;
  the simple `poly run image.txt` workload is what runs cleanly.

Debug aids: `JIT_DUMP_IR=1` (Cranelift IR per function),
`JIT_TRACE_CALLS=1` (per-dispatch trace), `JIT_ONLY_IDX=N` (install
just one entry).

End-to-end validation test:
`crates/polyml-jit/tests/jit_call_const_addr8_end_to_end.rs` —
caller pushes 7, calls JIT-cached closure via real
`CALL_CONST_ADDR8`, gets 107 back.

Plumbing: `Interpreter::install_jit`, `do_call` JIT-cache check
(gated by `!inside_jit`), `closure_call_trampoline` thread-local
routing, `jit_dispatch_closure_call` (with `MAX_JIT_DEPTH` cap).

## Open issues

- **JIT execution semantics on real code**: see "JIT status" above.
  Translation coverage is 60.12%; execution coverage is much less.
  Each install bisection reveals a separate semantic gap.

- **Remaining JIT translation gaps** (~40% of functions): CFG
  widening for the fall-through-deeper-than-recorded case (~190
  fns), dynamic CALL_CLOSURE arity (177 fns), and assorted niche
  opcodes (CASE16, BLOCK_EQUAL_BYTE, MOVE_TO_CONTAINER_B).

- **GC**: copying GC is in. The bump allocator behind it
  doesn't fragment; long-running programs stay under ~100 MB
  through the full bootstrap chain.

## Diagnostic tooling (use it!)

Before guessing at a bug, build a histogram. The hot-PC tooling
found the killer RESET_1 bug in ~30 minutes after weeks of
hand-tracing failed:

```rust
let interp = Interpreter::from_code_object(...)
    .with_default_alloc_space(...)
    .with_rts(rts)
    .enable_diagnostics();

// ...run...

let diag = interp.take_diagnostics().unwrap();
for ((code, off), cnt) in diag.hot_pcs(20) {
    println!("code=0x{code:016x}+{off:5} visits={cnt:10}");
}
```

CLI:
```
poly run --profile --trace-rts <image>
```

`--trace-rts` logs every RTS call; `--profile` prints a hot-code
histogram on exit. See `crates/polyml-runtime/tests/exec_bootstrap_profile.rs`
for a deeper-stop-and-dump example.

## HOL4 / SML experiment harness

Built 2026-05-30 to make SML reconstruction debugging repeatable (and to
survive a flaky terminal — one invocation yields the whole picture).

- `tools/sml-exp.sh [--steps N] [--cwd D] <checkpoint> <driver.sml>` —
  pipe an SML driver through `poly run <checkpoint>` and print ONE
  structured summary (result, fixpoint `LOADED_OK n/m` + stuck list,
  grouped compile diagnostics: undeclared structures/values, type
  errors, sig mismatches). Also writes a `.summary` next to the log.
- `tools/build-hol4-checkpoints.sh [--force] [basis|kernel|all]` —
  builds `/tmp/basis_loaded` (basis) and `/tmp/hol4_kernel` (basis +
  LCF kernel). The warm kernel image drops Theory-load iteration from
  ~3 min to ~15s.
- `crates/polyml-bin/tests/hol4_support/` — the captured HOL4 Theory
  reconstruction (was /tmp scratch): `build_kernel_checkpoint.sml`,
  `theory_subsystem.sml` (Net + real Overlay opaque re-ascription +
  HOLsexp/SHA1 stubs + Systeml stub + the ~54-file closure + fixpoint
  loader). Run standalone: `tools/sml-exp.sh /tmp/hol4_kernel
  crates/polyml-bin/tests/hol4_support/theory_subsystem.sml`.
- `crates/polyml-bin/tests/hol4_theory.rs` (+ `tests/common/mod.rs`) —
  `theory_subsystem_loads` (asserts ≥50/54), `theory_new_theory_runs`
  (`Theory.new_theory` executes — SUCCEEDS, REFL works), and
  `theory_dev_proof` (declares a type + consts + a schematic axiom on a
  user theory, then derives `|- mul e (mul e x) = x` via `Thm.INST` +
  `Thm.TRANS` — real theorem development beyond the kernel primitives, no
  Parse needed). `#[ignore]`; needs `/tmp/hol4_kernel`. `common/mod.rs`
  has the reusable `run_theory_subsystem` + `classify_errors`/`parse_loaded`
  helpers. `tools/closure-probe.sh <ckpt> <dir>…` is a generic "how far
  does this subsystem load?" probe (enumerate + fixpoint-load + summarize).
  ```sh
  cargo build --release -p polyml-bin
  tools/build-hol4-checkpoints.sh
  cargo test --release -p polyml-bin --test hol4_theory -- --ignored --nocapture
  ```

Two runtime gaps this work surfaced (both real, worth fixing):
1. **`OS.Process.getEnv` returns `SOME ""`** for set env vars (stubbed/
   broken) — so HOL paths must be passed by other means (we use the
   `../hol4` relative path from cwd = `vendor/polyml`).
2. **An uncaught exception propagating through a single `PolyML.use`**
   trips the "exception packet being called as a closure → call to
   non-closure value" halt (interpreter exception-unwinding bug). Piping
   source per-declaration to the REPL avoids it (each top-level decl is
   handled independently). `run_theory_subsystem` pipes for this reason.

HOL4 Theory subsystem status: 50/54 modules compile + load + run on the
interpreter (the 4 stuck are the theorem-DB *search* layer: DB /
DBSearchParser / TheoryReader — DBSearchParser needs the `regexpMatch`
library which isn't vendored). See the per-project exo-self notes
(2026-05-30) for the full dependency archaeology and the keystone fix
(Thm.hash leak hidden by Overlay's opaque `open Kernel`).

HOL4 **term/type parser status: WORKING** (2026-06-04). The full
`src/parse` core — 79/79 modules including `term_grammar`, `Pretype`,
`Preterm`, `Absyn`, `parse_type`, `parse_term`, `Overload`, `term_pp`,
`type_pp`, `Parse` — compiles, loads, and *runs* on the interpreter.
`Parse.Term [QUOTE "\\x. x"]` and `Parse.Type [QUOTE ":'a -> 'a"]` parse
real quotations into HOL4 terms/types (see `crates/polyml-bin/tests/
hol4_parse.rs`). Build the warm checkpoint with
`tools/build-hol4-checkpoints.sh parse` → `/tmp/hol4_parse` (chain:
basis → kernel → theory → parse; the script gates the export on a
Parse.Term/Parse.Type smoke test). `base_lexer.sml` IS checked in
(ml-lex-generated, loads cleanly — the historical "generated-lexer wall"
does not apply), and `term_tokens.sml` is rewritten to `\DDD` escapes so
our ≥0x80-rejecting string lexer accepts it.

**The keystone was a missing pervasive `Interrupt`** (root-caused
2026-06-04, not the earlier "Interrupt-dispatch" red herring). Real
PolyML installs Interrupt/Bind/Match into the INITIAL top-level namespace
(`mlsource/MLCompiler/INITIALISE_.ML:524`); `basis/General.sml` re-binds
Bind/Match/Overflow/etc. at top level but **NOT Interrupt**, and our
checkpoint export/reload drops the compiler-pervasive one — so a bare
`Interrupt` was *unbound* on our checkpoints. HOL4's
`src/portableML/Portable.sml` uses `... handle Interrupt => raise
Interrupt | _ => NONE` for `Lib.total` / `Lib.can` / `with_exn`; with
`Interrupt` unbound those parse as a catch-all **variable** pattern that
re-raises everything, so `total`/`can` never returned `NONE`. That
silently broke `term_grammar`'s `min_grammar` build
(`Overload.add_overloading` → `strip_comb` → `total dest_comb` re-raised
"not a comb") and ~22 downstream parse modules. Fix: one line in
`build_kernel_checkpoint.sml` — `exception Interrupt = RunCall.Interrupt;`
before `Portable.sml` compiles. (Two smaller leaf fixes rode along:
`Systeml.OS` for `type_pp.sml:15`, and the `AList`/`Graph`/`SymGraph`/
`ImplicitGraph` graph libs for `AncestryData.sml`.)

HOL4 **bool theory + tactic layer: WORKING** (2026-06-04). Goal-directed
tactic proofs run on the interpreter: `Tactical.prove(``p ==> p``,
DISCH_TAC THEN POP_ASSUM ACCEPT_TAC)`, conjunction-commutativity, and a
K-combinator goal all prove (see `crates/polyml-bin/tests/hol4_tactic.rs`).
The chain is now basis → kernel → theory → parse → **bool → tactic**, all
built by `tools/build-hol4-checkpoints.sh` (targets `bool` → `/tmp/hol4_bool`,
`tactic` → `/tmp/hol4_tactic`).

Two things made `boolScript.sml` (modern `Theory bool[bare]` + `“…”`
quotations) loadable without an external toolchain:
1. **The quote-filter runs on our interpreter.** HOL4's *modern* filter
   (`tools/parsing/HOLSource{AST,Parser,Expand,Printer}` + `DString`/`DArray`/
   `AttributeSyntax`/`SimpleBuffer`) is hand-written SML, NOT ml-lex/yacc
   generated (the lone `.lex`, `HolLex`, feeds only the *legacy*
   `HolParserOld`). `build_bool_checkpoint.sml` loads the 16 filter modules
   (one fix: `Systeml.canBindStr`) and runs `HOLSource.inputFile` on the real
   `boolScript.sml` → 175 KB of plain ASCII (in-body unicode becomes `\DDD`
   escapes via `HOLSourcePrinter.encodeStr`, so the ≥0x80 string-lexer gate is
   never hit). No sed/Rust preprocessor; no string-lexer change.
2. **`export_theory` is neutralized, `structure boolTheory` synthesized.**
   `Theory.export_theory()` does heavy FS finalize (`OS.FileSys.getDir`, path
   ops, writes) that raises → trips the exn-unwinding halt; we don't need the
   on-disk `.dat`/generated `.sml`, only the in-memory segment, so we rewrite
   `export_theory`→`current_theory` (no-op) in the filtered source and build
   `structure boolTheory` (191 names) ourselves from
   `Theory.current_{axioms,definitions,theorems}()`.
The tactic layer then needs three small props: `structure Definition =
Theory.Definition`, a thin `structure DB` over `DB_dtype` (the full
DB search layer — `DBSearchParser`/`regexpMatch` — is NOT needed), and
`val explode = String.explode` (our checkpoint leaked `Portable.explode`
= string-list to the top-level pervasive; `Conv.sml`'s `dest_path` wants the
SML-default char-list `explode`). The src/1 leaves loaded: `thmpos_dtype`,
`Rsyntax`, `Psyntax`, `FullUnify`, `resolve_then`, `mp_then`. 27/27 of the
core chain load (`boolSyntax`…`Tactic`).

HOL4 **REWRITE_TAC (rewriting engine): WORKING** (2026-06-04). `REWRITE_TAC []`
simplifies boolean goals via the default rewrite set (11 boolTheory clauses,
`Rewrite.implicit_rewrites`), and `REWRITE_TAC [thm]`, `ASM_REWRITE_TAC`,
`ONCE_REWRITE_TAC` all run (`crates/polyml-bin/tests/hol4_rewrite.rs`:
`⊢ T ∧ p ⇔ p`, `⊢ p ∨ T`, `⊢ ¬¬p ⇔ p`, `⊢ p ⇒ p ∧ T`). The engine is just
4 files — `BoundedRewrites.{sig,sml}` + `Rewrite.{sig,sml}` — on top of
`/tmp/hol4_tactic` (`Net` + `Conv.REWR_CONV` are already present); built by
`tools/build-hol4-checkpoints.sh rewrite` → `/tmp/hol4_rewrite`. (Higher-order
`Ho_Net`/`Ho_Rewrite` load cleanly too but aren't needed for plain REWRITE_TAC.)

**Building theories above bool now works** (the `new_theory` export keystone,
2026-06-04). `Theory.new_theory` on a NON-empty base implicitly exports the
current segment to disk first (`Theory.sml:1178`), and that PP-to-file path
trips the interpreter's exception-unwinding VM halt — bool only built because it
came off the *empty* scratch segment (no-export branch). Fix: the public
`export_theory` already gates on `Globals.interactive`; we made `new_theory`'s
*implicit* export honor it too (`Theory.sml:1178` patch) and set
`Globals.interactive := true` in `build_kernel_checkpoint.sml`. We drive HOL4 as
a REPL and never write `.dat`, so this is faithful. **markerTheory is built**
this way (`build_marker_checkpoint.sml` → `/tmp/hol4_marker`, all 29
defs/theorems via real tactics). Two reusable pieces: a synthesized
`structure boolLib` (the real one won't load — `grammarDB{bool}=NONE` + backtick
quotes) + tactic infixes; and `Theory.register_replayed_axiom` for the ancestor
(bool) axioms before `new_theory` (our synthesized `boolTheory` keeps each
theorem's live axiom-nonce tag, unlike disk `DISK_THM`, so `uptodate_axioms`
needs the nonces registered).

Roadmap toward full automation (mapped 2026-06-04, first wall on each step):
- `REWRITE_TAC [thm]`/`ASM_REWRITE_TAC`/`ONCE_REWRITE_TAC` — DONE.
- `new_theory` on a non-empty base — DONE (keystone above).
- `markerTheory` — DONE (`/tmp/hol4_marker`).
- `combinTheory` — DONE (`/tmp/hol4_combin`, `build_combin_checkpoint.sml`).
  combinScript only *opens* `computeLib`/`combinpp` (never calls them), so they're
  stubbed (+ a no-op `compute` ThmAttribute, since `boolLib.save_thm_attrs` raises
  on unknown attrs); the real leaf needed was `src/q/Q`. Avoids the heavy
  computeLib/clauses/TypeBase closure. `combinTheory.I_THM = ⊢ ∀x. I x = x`.
- `SIMP_TAC`/`simpLib` — DONE (`/tmp/hol4_simp`, `build_simp_checkpoint.sml`,
  `hol4_simp.rs`). `SIMP_CONV ss [] ``(I:'a->'a) x = x`` = ⊢ (I x = x) ⇔ T` and
  `prove(``(I:'a->'a) x = x``, SIMP_TAC ss [])` = `⊢ I x = x`, with a hand-rolled
  `simpLib.empty_ss ++ rewrites [combinTheory.I_THM, AND_CLAUSES, REFL_CLAUSE]`.
  Assembled on `/tmp/hol4_combin` (33 files): leaves (`Hol_pp` w/ expanded DB
  stub, `term_tactic`, `Ho_Net`, `ParseExtras`, `Ho_Rewrite`, `Prim_rec`
  [grammarDB{bool} valOf → global Parse], `liteLib`, `AC`, `simpfrag`) + real
  `markerSyntax` + the 5 simp-core modules + TYPED STUBS for `markerLib`
  (15 names; real one needs the absent `proofManagerLib`) and `TypeBasePure`/
  `TypeBase` (simpLib only type-checks `ty_name_of`/`simpls_of`/`fetch`).
  Footgun: synthesized boolLib's `open Theory` shadows the *function* `pp_thm`
  with `Theory.pp_thm` (a ref) — re-export `val pp_thm = Hol_pp.pp_thm`. The full
  default `bool_ss` (UNWIND_ss → `Unwind`→`refuteLib`/`Canon`/`tautLib`→
  `HolSatLib` SAT subsystem; `Canon` also has backtick quotes) is NOT built — a
  hand-rolled simpset suffices and avoids those walls.
- **`numTheory` + INDUCTION — DONE** (`/tmp/hol4_num`, `build_num_checkpoint.sml`,
  `hol4_induction.rs`). `numScript.sml` builds via the recipe and bootstraps the
  naturals + `numTheory.INDUCTION` from `boolTheory.INFINITY_AX`. With HOL4's
  generic `src/1/Prim_rec` (INDUCT_THEN takes the induction theorem as an arg —
  no prim_recTheory needed) and `INDUCT_TAC = Prim_rec.INDUCT_THEN
  numTheory.INDUCTION Tactic.ASSUME_TAC`, genuine induction proofs run:
  `⊢ ∀n. n = 0 ∨ ∃m. n = SUC m` and `⊢ ∀n. ¬(SUC n = n)`.
- **`⊢ ∀n. n + 0 = n` — DONE** (`num_arith_trophy.sml`, `hol4_induction.rs::
  arithmetic_induction_n_plus_0`). The canonical arithmetic induction, proved BY
  HAND on `/tmp/hol4_num` — the "multi-day SAT/bool_ss wall" was **sidesteppable**:
  `UNIQUE_SKOLEM_THM` → `num_Axiom` (primitive recursion) → `add` (via
  `num_Axiom` + `new_specification`) → `INDUCT_TAC`, with NO bool_ss, NO SAT
  subsystem, NO relationTheory, no `Prim_rec`. Two reusable techniques:
  (1) **plain `REWRITE_TAC` is first-order** — it can't rewrite with the
  higher-order `FORALL_AND_THM`/`SKOLEM_THM`/`EXISTS_UNIQUE_THM`; use
  `Conv.HO_REWR_CONV` under `TOP_DEPTH_CONV` (this is what `bool_ss` was really
  providing for UNIQUE_SKOLEM_THM). (2) `LESS_THM` is provable **TC-free**
  (induction + `num_CASES` + `LESS_MONO_REV`), so `<` needs no `relationTheory`.
  With `num_Axiom` in hand, recursive function definitions over ℕ are reachable
  (direct `num_Axiom` + `new_specification`) without the SAT path.
- `bossLib`/`BasicProvers` — the remaining campaign: a faithful `bool_ss`/
  `SIMP_TAC` (its `UNWIND_ss` → the SAT subsystem `HolSatLib`; but the arithmetic
  result above shows HO-conversions can replace `bool_ss` for many proofs),
  `Datatype`/`TotalDefn`, and the pair/pred_set/list/option `*Script.sml`
  theories (all reuse the recipe). Broader "real mathematics" opens up here.

- **Arithmetic library — DONE** (`/tmp/hol4_arith`, `build_arith_checkpoint.sml`,
  `hol4_arith.rs`, `structure numArith`). `add`/`mult`/`EVEN`/`ODD` defined from
  `num_Axiom` (no Prim_rec), and the Peano laws proved by `INDUCT_TAC` (no
  bool_ss/SAT): `ADD_COMM`, `ADD_ASSOC`, `ADD_RCANCEL`, `ADD_EQ_0`, `MULT_COMM`,
  `RIGHT_ADD_DISTRIB`, and the parity headline `⊢ ∀m n. EVEN (m+n) ⇔ (EVEN m ⇔
  EVEN n)`. This is genuine "real mathematics by induction" on the interpreter.

The HOL4 ladder so far (each a `build-hol4-checkpoints.sh` target + an
`#[ignore]` regression test): kernel → theory → parse → bool → tactic → rewrite
→ marker → combin → simp → num → arith. Headline proofs on `/tmp/hol4_simp`:
the Drinker Paradox `⊢ ∃x. D x ⇒ ∀y. D y`, quantifier duality, `S K K = I`
(`hol4_fancy.rs`); on `/tmp/hol4_num`: induction over ℕ (`hol4_induction.rs`);
on `/tmp/hol4_arith`: ADD_COMM/MULT_COMM/EVEN_ADD (`hol4_arith.rs`).
`theory_dev_proof` remains the kernel-level proof. `tools/closure-probe.sh
/tmp/hol4_theory src/parse` measures parse-layer load on the Theory base.

## RTS calling conventions

The most common cause of arity-mismatch bugs:

| SML wrapper      | C signature           | Our arity |
| ---------------- | --------------------- | --------- |
| `rtsCallFastN`   | N args, no threadId   | Arity-N   |
| `rtsCallFullN`   | (threadId, N args)    | Arity-(N+1) |
| `rtsCallFast0 "X"` invoking `unit -> ?` | C is `(void)` but SML passes unit | Arity1 |

The last row is the gotcha: PolyML's C side accepts the extra arg
silently because x86-64 ignores unused register args. Our typed
dispatch must match the call site exactly.

## Where the upstream reference lives

`vendor/polyml/libpolyml/bytecode.cpp` is the bytecode dispatcher
we're porting. Keep cross-references in comments — every non-trivial
opcode handler in `crates/polyml-runtime/src/interpreter/mod.rs`
cites the upstream line range.

## Don't merge RESET variants

`INSTR_RESET_N` (drop top N) and `INSTR_RESET_R_N` (preserve top,
drop N below) look identical but aren't. Merging them silently
corrupts every loop using RESET to discard a result. See the comment
in `mod.rs` around `INSTR_RESET_1 => self.drop_n(1)`.
