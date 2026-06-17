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
| Basis load (`Bootstrap.use "basis/build.sml"`) | 19s | 1.8B | 95M |
| Full 7-stage chain                    | 5min   | 27.7B    | 92M       |
| HOL4 kernel + 14 inferences proof     | 15s    | ?        | ?         |

Three structural fixes account for most of the gain:
1. `gc_threshold_percent()` cached in `AtomicUsize` — was reading
   env var on every step → 6.2x.
2. Pre-computed `gc_trigger_words` from `cap * threshold / 100`,
   plus `#[inline(always)]` + `get_unchecked` on push/pop/peek/
   reset/drop_n → 1.35x more.
3. **In-crate `run_until` loop** (2026-06-16, commit d2bc443, task #88
   lever 1): the CLI used to call `step()` per opcode across the crate
   boundary, and `step()` ran three always-off debug checks before every
   dispatch (`arbint_trace_on()` atomic, `diag` Option, `is_traced()`
   atomic). Split `step()` into `step_impl<const INSTR: bool>` (debug
   paths gated on `INSTR`, compiled out in production) + an in-crate
   `run_until(max_steps)` that picks the fast monomorphisation once.
   GC/finish cadence byte-identical. **Measured ~12% on the basis load
   (84.5 → 95.4M steps/sec, byte-identical 1.783B-step trace).** The
   number below reflects this.

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

**Current coverage**: 3,410 / 4,436 code objects translate (76.9%),
**727 install** (2026-06-12; was 592 on 2026-05-28, then 612, then 727
after the TAIL_B_B fix below). The install filter rejects functions
whose bytecode contains opcodes whose translations we don't yet trust.
The 60% → 73% jump (2026-05-28) implemented STACK_CONTAINER_B (+122),
LOCK/CLEAR_MUTABLE (+170), BLOCK_EQUAL_BYTE (+65), GET_THREAD_ID (+16),
and a handful of smaller opcodes; CASE16 added +97 translate (2026-06-12);
TAIL_B_B added +115 install (2026-06-12).

The opcodes we currently SKIP at install time (`install_all_jit_entries`
in `polyml-jit/src/lib.rs`):
- CALL_LOCAL_B (0x16) — peek-don't-pop calling convention our
  trampoline path doesn't fully model (it deliberately over-pushes
  and reuses leftover slots after the call returns, so `n_args` can't
  be inferred statically — unlike TAIL_B_B, which forwards exactly its
  args).
- CALL_CONST_ADDR variants (0x57/0x58/0x17/0x18) — translation
  loads closure pointer at runtime, but the call still SEGVs
  downstream in unisolated cases.

TAIL_B_B (0x7b) — **NOW INSTALLS** (2026-06-12, +115 functions, the
next perf lever after CASE16). It was SKIPPED because "re-enabling
breaks the basis-loaded HOL4 workload" — root-caused by a 3-seat
ultracode fleet (all three converged on the SAME bug independently):
the JIT translation popped the tail-call group in the WRONG ORDER. The
group is `[retPC, closure, args...]` top→bottom (mirrors do_tail_call,
mod.rs:3757 / upstream bytecode.cpp:387-406); the old code popped
`tail_count-2` items off the top as args FIRST, then grabbed the next
slot as the "closure" — so it never discarded the retPC placeholder and
dispatched a real data arg (a tagged int) AS the closure → "call to
non-closure value: Tagged(0)" / SEGV on tail-recursive code
(List.map/tabF, DATATYPE_REP constructors). Fix (translate.rs
INSTR_TAIL_B_B): pop+discard the retPC placeholder, then the closure,
then the N args; underflow guard widened to `tail_count` in both the
translate path and scan_one_opcode. The `skip` immediate is correctly
ignored — it only governs in-place caller-frame collapse on the
interpreter's shared PolyWord stack; the JIT returns the callee result
directly. NOT an arity bug: `JIT_TRAMP_VERIFY_ARITY=1` reports ZERO
mismatches across the full 1.675B-step basis load, so tail_count-2 ==
callee arity always. Verified: simple bootstrap Tagged(0), the full
basis load under --jit Tagged(0) (the gate that was failing), and a
JIT==interp differential with a negative control
(`tests/tail_b_b_differential.rs`).

**PERF REALITY CHECK (measured 2026-06-12 — read before doing ANY more
JIT perf work).** `--jit` with 727 installs is ~5% SLOWER than the plain
interpreter on the basis load (25.2s vs 24.1s, 3 runs each). Two levers
were investigated and BOTH ruled out as the bottleneck:

1. *Nested JIT→JIT dispatch* — NOT the problem. Probing `MAX_JIT_DEPTH =
   256` (see jit_bridge.rs) runs the simple bootstrap AND the basis load
   (deep recursion) to Tagged(0) with no SEGV/overflow — the old
   "install=53 SEGV" is already fixed (same wrong-args family as
   TAIL_B_B). But enabling nesting is PERF-NEUTRAL: 25.3s vs 25.2s.

2. The actual binding constraint is **hot-function COVERAGE**. `poly run
   --jit --profile` shows total CALL JIT-cache hit rate ≈ **1.6%**, and
   the **top-10 most-called functions are ALL 0.0% JIT** — the 727 we
   install are the COLD periphery; the genuinely hot functions can't be
   installed (or even translated) because they contain still-blocked
   opcodes. The profiler's per-function blocker analysis names the mix:
   CALL_LOCAL_B, CALL_CONST_ADDR8_0, the untranslatable CASE16 tail
   (the 4/25 that hit ESCAPE), STACK_CONTAINER_B variants, TAIL_B_B
   *coexisting* with another blocker. There is NO single silver-bullet
   opcode — the hot functions typically have MULTIPLE blockers, so
   clearing one doesn't install them.

So a real JIT speedup is a MULTI-FRONT effort (clear CALL_LOCAL_B +
CALL_CONST_ADDR + the CASE16/ESCAPE tail + CALL_CLOSURE, all of them, on
the same hot functions) with UNCERTAIN payoff — the trampoline-boundary
cost + Cranelift-vs-a-tuned-92M-steps/sec-interpreter means even full
coverage might not win. The honest current value of the JIT is as a
translation/execution **correctness testbed** (the differential harness,
opcode semantics), not throughput. Don't chase "+N installed opcodes"
expecting "+speed" without first re-profiling the cache-hit rate on the
HOT path.

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
- CASE16 (0x0a) — NOW TRANSLATES (2026-06-12, commit 65bf0ed): 21/25
  CASE16 code objects in the bootstrap translate, +97 functions overall
  (3313→3410). The old `Underflow` was NOT the linear-depth-scan in
  `scan_branch_targets` (that hypothesis measured to gain 0) — it was two
  other bugs: (1) `infer_arg_count` was CFG-blind (stopped at CASE16's
  `_ =>` arm, under-counting args → case bodies entered too shallow →
  Underflow) — now a worklist/CFG pass enqueuing CASE16's N targets +
  default at post-pop depth; (2) Cranelift `br_table` needs an i32 UNSIGNED
  index but the untagged selector is i64 — now range-guarded (0≤u<arg1,
  matching mod.rs:2125) + ireduce to i32. Verified JIT==interp
  (tests/case16_differential.rs) on every selector incl. out-of-range. The
  4 remaining CASE16 fns fail on the harder 0xfd/0xfe (ESCAPE) class.
  Profiling found this: the hottest bootstrap/Isabelle-compile code object
  (21% of all steps) was a CASE16 fn — the biggest single perf lever.
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

## Differential testing against upstream PolyML (the oracle — use it!)

Built 2026-06-09. The foundation audit's deepest lesson was that latent bugs
hide everywhere with no systematic detector — every Isabelle keystone turned
out to be a runtime bug that had been silently wrong. The fix is a *ground-truth
oracle*: run the same SML through the real upstream PolyML and through our `poly
run`, diff the results. Any difference is a faithfulness bug in OUR port.

- `tools/build-oracle.sh` → builds upstream PolyML at `/tmp/polybuild/poly`
  (out-of-tree; vendor stays pristine). Default int config (FixedInt 63-bit,
  `Int.maxInt = 4611686018427387903`) MATCHES `/tmp/basis_loaded` — so that
  checkpoint is the right diff target (NOT `/tmp/arbint_image`).
- `tools/build-oracle.sh interp` → builds upstream with the BYTECODE interpreter
  (`--enable-native-codegeneration=no`) at `/tmp/polybuild-interp/poly`. Same
  bytecode backend + format as us → the reference for differential CODEGEN
  debugging (it proved the andb/orb bug is our build's compiler-execution, not
  the backend source).
- `tools/diff-oracle.sh [--dir <d>] <file.sml ...>` runs each snippet through
  both and compares `@@<label>=<value>` lines (the filter strips REPL chatter).
- `tools/diff-corpus/*.sml` — ~1600 deterministic comparisons across 45 files
  (30 Basis categories + compiler-stress programs, incl. `cstress_heavy.sml`:
  heavy-compute stress — Ackermann/naive-fib call storms, 100k-deep mutual TCO,
  bignum factorials/powers/gcd/powmod + GC pressure, 100k-element folds, and
  exception raise/handle loops — all byte-identical to upstream). Run:
  `tools/diff-oracle.sh --dir tools/diff-corpus` (wired into `regression.sh full`).
  The 2026-06-16 faithfulness sweep (ultracode wf_a7f8686d-310) added 317
  edge-case comparisons in `numeric_edge.sml` (divMod/quotRem sign conventions,
  IntInf.pow/divMod corners, Word shifts at/beyond wordSize), `real_edge.sml`
  (inf/nan/subnormal classify, the full Real.toLargeInt rounding matrix,
  copySign/nextAfter, Real32 paths), `text_edge.sml` (Char.chr/escape
  boundaries, String.collate/tokens/translate/scan, Substring), and
  `struct_edge.sml` (List/Vector/Array/ListPair edge + exception cases,
  ref-vs-structural equality, exnName/exnMessage, functor/signature/record/
  exception-payload compiler stress) — ALL byte-identical to upstream (0
  divergences, triaged + independently re-verified through both the native and
  bytecode-interp oracles).

**Verdict (2026-06-09, final):** the interpreter is FAITHFUL to upstream on all
~1300 cases. The one apparent divergence (`IntInf.andb`/`orb` with a short operand
in the special-case slot: `andb(~1,2^80)=0`) turned out to be a **latent UPSTREAM
bug**: the stage-0 bootstrap compiler (`bootstrap64.txt`, a checked-in image from
an older PolyML) mis-specializes andb/orb when compiling the basis. Upstream's own
`polyimport` over the same stage-0 image + same `basis/build.sml` emits the
BYTE-IDENTICAL wrong bytecode and computes the SAME wrong answers; upstream's
shipped `poly` is unaffected only because its basis is recompiled by the stage-2+
self-compiled compiler (full 7-stage chain) — and our self-bootstrapped
`vendor/polyml/polyexport` (the chain run on OUR runtime) likewise has the correct
form. So we reproduce upstream's stage-0 behavior *including its bug, byte for
byte* — the strongest faithfulness statement available. The corpus `intinf`
divergence is an artifact of comparing our stage-0-built basis against their
stage-N-built poly. See `docs/differential-oracle-2026-06-09.md` (RESOLVED
section). The interp-vs-JIT differential is clean (40/40).

A bytecode dumper (`/tmp/dump.sml` pattern: closure word0 → code obj →
`RunCall.loadByte`) + the `disasm` module (`crates/polyml-runtime/src/interpreter/
disasm.rs`) decode a function's bytecode for codegen forensics.

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

Two runtime gaps this work surfaced:
1. **`OS.Process.getEnv` — FIXED** (commit 3930551). Was a hard stub that
   returned `SOME ""` for every variable; now reads `std::env::var` and raises
   a real `SysErr` packet on miss, so set vars return `SOME value` and unset
   return `NONE`. (Historically HOL paths were passed via the `../hol4` relative
   path from cwd = `vendor/polyml`; `HOL4_DIR` now works too.)
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
- **The SAT subsystem is NOT a blocker** (corrected 2026-06-05; the earlier
  "Datatype BLOCKED on SAT" finding was wrong). `HolSatLib` does NOT require an
  external `minisat`: `minisatProve.invoke_solver` gates the external binary on
  `access(getSolverExe solver,[A_EXEC])` (`minisatProve.sml:60`); the binary is
  absent (only C++ source is vendored), our `fs_access` returns false, and the
  call falls through to HOL4's **pure-SML `DPLL_TAUT` prover** (`dpll.sml`) —
  genuine kernel inference, no shell-out, no `Process.system`. The only real RTS
  gaps were `OS.FileSys.tmpName`/`remove` (the DIMACS temp file `dimacsTools`
  writes *before* the DPLL fallback fires) + `OS.Process.getEnv` (was a `SOME ""`
  stub) — all fixed in `rts.rs` (commits 3930551 / 68f253c). **`tautLib.TAUT_PROVE`
  now runs on the interpreter** (`/tmp/hol4_taut`, `build_taut_checkpoint.sml`,
  `hol4_taut.rs`): proves `p ∨ ¬p`, De Morgan, hypothetical syllogism, Peirce's
  law via DPLL. Recipe: build `satTheory` (truth-table tautologies, Script→Theory),
  load the HolSat closure + `tautLib` (with the `grammarDB{bool}` patch + a
  `minisatParse` stub for the dead external-replay path).
- **`mesonLib` (first-order automated proving) — DONE** (`/tmp/hol4_meson`,
  `build_meson_checkpoint.sml`, `hol4_meson.rs`). `MESON_TAC` (HOL4's model-
  elimination prover — Skolemizes, instantiates quantifiers by unification,
  chains inferences) runs on the interpreter, cascading from the SAT fix
  (mesonLib `open`s tautLib at load). Built on `/tmp/hol4_simp` (carries
  `liteLib`+`Ho_Rewrite`): shadow simp's boolLib with the widened one from
  build_combin (for `save_thm_at`), replay the taut layer, then load
  `Canon_Port`/`jrhTactics`/`mesonLib` — the first two of which carry `` `…` ``
  quotations so they go through the `HOLSource` quote-filter, plus the
  `grammarDB{combin}`/`grammarDB{bool}` → global-Parse patch. Proves the drinker
  paradox, a predicate syllogism, and a symmetric+transitive relation goal via
  genuine first-order reasoning. NOTE the quote-filter trick: `HOLSource.inputFile`
  works on plain `.sml` (not just Theory scripts), converting `` ``…`` `` term
  quotations to `[QUOTE …]` — this unblocks any quotation-carrying HOL4 `.sml`.
- **METIS (`metisLib` / `METIS_TAC`) — DONE** (`/tmp/hol4_metis`,
  `build_metis_checkpoint.sml`, `hol4_metis.rs`, 2026-06-06). HOL4's strongest
  first-order prover (Joe Hurd's resolution + paramodulation) runs on the
  interpreter: `METIS_TAC` proves equality/paramodulation goals MESON can't —
  `AC_CHAIN` (4-deep product reversal from comm+assoc, the HOL4 README's own
  showcase), equality congruence, FOL syllogisms — each a verified 0-hyp theorem.
  The finish was the **full `bool_ss`**: make the build_simp `markerLib` stub's
  REWRITING functions (`Cong`/`unCong`/`AC`/`unAC`/`TIDY_ABBREV_CONV`) REAL — tiny
  kernel ops over `markerTheory` — so `simpLib` is compiled against a real `Cong`
  and full `bool_ss` loads (the heavy suspended-goal/`proofManagerLib` machinery
  stays stubbed; `bool_ss` never touches it). Then the 33-module `mlib*` core +
  `Canon`/`refuteLib`/`Unwind`/`BoolExtractShared`/`pureSimps` + `normalFormsTheory`
  (Script→Theory) + `normalForms`/`folTools`/`metisTools`/`metisLib`, with the usual
  patches (grammarDB, COND_BOOL_CLAUSES, DB.fetch table, HOLSource quote-filter) and
  one tactic patch (COND_COND → case-split: our simp doesn't rewrite CONDs through
  atomic-bool assumptions). Needs the realToInt interpreter fix (e4800cf) +
  portableML `Intset`/`Intmap`. CAVEAT: mlib's time-slice scheduler vs our timing
  → cumulative/heavy proving in ONE process can hit a spurious `Time` exception
  (mlibOmega's `Time.fromSeconds`); resets per fresh image, NOT a soundness issue,
  so prove one goal-group per process. Earlier "blocked on proofManagerLib" was
  overblown — the real markerLib only uses it in one interactive helper.
- **`Datatype` package — DONE (2026-06-11, task #68). The whole stack RUNS.**
  `Datatype.Datatype [QUOTE "tree = Leaf | Node tree tree"]` builds the type +
  constructors, generates structural induction + case nchotomy + the recursion
  theorem, and registers it in TypeBase; then `Define`/`tDefine` define
  (recursive, incl. non-structural) functions over it. Final checkpoint
  `/tmp/hol4_datatype` (build target `datatype`, `hol4_datatype.rs`); full chain
  kernel→…→numsimps→pair→sum→one→option→**defn**(Define)→**numpair**→
  **ind_type**(JRH `define_type`, 41/41)→**Datatype**. The staged roadmap below
  is kept as the historical build record; its "UNCERTAIN/HARD" labels are
  superseded — every stage landed. **Original staged path** from `/tmp/hol4_metis`
  (build each via the Script→Theory recipe, checkpoint each layer):
  - **Stage 0 — DONE**: real `numTheory` on the prover base. `build_num` re-based on
    `/tmp/hol4_metis`; `/tmp/hol4_num` now has real `numScript` INDUCTION + live
    `bool_ss`(∃!)/`MESON`/`METIS`; arith/order rebuild on it (`hol4_num_prover.rs`).
  - **Stage 1 — DONE** (2026-06-09): the REAL `prim_recTheory` on `/tmp/hol4_prim_rec`
    (`build_prim_rec_checkpoint.sml`, target `prim`, test `hol4_prim_rec.rs`). The
    actual `prim_recScript.sml` runs quote-filtered and split at decl boundaries,
    with three trophy-proof splices: TC-free `LESS_LEMMA1`, the hand-proved
    `UNIQUE_SKOLEM_THM`+`HO_REWR_CONV` SIMP_REC specification, and the trophy
    `SIMP_REC_THM` (upstream's AP_TERM_TAC step fails here). TC block + WF tail cut
    (return with relationTheory at Stage 2-3); `local open BasicProvers` dropped;
    TypeBase.export cut. 37 names; `num_Axiom`/`PRIM_REC_THM`/`LESS_THM` all
    hypothesis-free; `define_case_constant num_Axiom` (num_case_def) WORKS. Two
    new-found footguns: the filter's `Theorem x = expr` form needs
    `boolLib.save_thm_at` (widen the narrow synthesized boolLib); never name a
    build-script helper `U` (part1's `open HolKernel` rebinds Lib's list-union over
    it for all later decls).
  - **Stage 2 — PARTIAL (2026-06-09)**: `/tmp/hol4_relation`
    (`build_relation_checkpoint.sml`) carries the COMPLETE arithmetic-critical
    fragment — TC/RTC (rules/induct/cases, EXTEND_RTC_TC*) + reflexive/symmetric/
    transitive_def + WF core (WF_DEF, WF_INDUCTION_THM) — built from the real
    relationScript with a BasicProvers SHIM (srw_ss=bool_ss ref; SRW/RW_TAC =
    strip+FULL_SIMP+ASM_REWRITE-closer; PROVE_TAC=ASM_MESON; `by`=Q.SUBGOAL_THEN;
    Induct_on = rule-induction via the REAL IndDefLib map). **IndDefLib loads and
    runs for real** (Inductive RTC → xHol_reln works; InductiveDefinition
    quote-filtered + grammarDB patch; ThmSetData on a widened DB stub) — Stage 8's
    core, banked early. 2026-06-10: WFREC LANDED via the per-theorem sweep (relation_tail_sweep.sml; builder chains build→sweep→promote): 186 names incl. WFREC_THM/WF_RECURSION_THM/WFP/WF_inv_image — the Define foundation is banked. Remaining: the EQC tail + WF_PULL
    (real-SRW coupling) and the inv_image/WFREC tail (gates `Define`; the
    attr-strip save_thm_at fix is in, the WFREC run needs a longer step budget /
    per-theorem splits). Real TypeBase/TypeBasePure + BasicProvers stay Stage 3. HARD→IN PROGRESS.
  - Stage 4 — `numeralTheory` + `arithmeticTheory` (5759 lines, 81 METIS — watch the
    METIS cumulative Time-exception; split or swap small METIS_PROVE→MESON). UNCERTAIN.
  - Stage 5 — `computeLib` (first build ever) + `reduceLib` + `numSimps` (~25 pure-SML
    modules, no minisat; sidestep `cv` via legacy `conv-old/Arithconv`). UNCERTAIN.
  - Stage 6 — `numpairTheory` (heaviest; needs `numSimps` + `TotalDefn`/`Define`, or a
    minimal `nfst/nsnd` sidestep). HARD — the biggest structural risk.
  - Stage 7-9 — `ind_typeTheory` (light: 18 SIMP/1 MESON) + `InductiveDefinition`/
    `IndDef` (hand-rolled MONO_TAC, no MESON; quote-filter + grammarDB patch) +
    `Datatype` assembly (`ParseDatatype`/`RecordType`/`DataSize`). LIKELY once the
    arithmetic middle exists. SMOKE: `Datatype \`tree = Leaf | Node tree tree\`` →
    check generated induction/recursion theorems.
  Bottom line (RETROSPECT): the arithmetic middle (relation→arithmetic→numeral→
  numSimps) was indeed the cost, built via the per-theorem sweep harness; the
  ind_type/Datatype top assembled cleanly once it existed. All landed 2026-06-11.

- **Verified programs on the Datatype package** (the capstones — what it's FOR;
  all on `/tmp/hol4_datatype`, all in `hol4_datatype.rs`, all fenced by
  `regression.sh full`). NOTE: this checkpoint has NO `listTheory` (no `::`/`[]`/
  `:num list`), so every list-like type is a USER datatype (e.g. `lst = Nil |
  Cons num lst`). Numeral arithmetic in **computeLib EVAL now reduces `*`**
  (`3*4 → 12`): the numeral sweep had banked degraded DB theorems
  (`DB.fetch "numeral" "numeral_distrib" = ⊢ T`), so the global compset could
  pull `NUMERAL` out over `*` but not reduce the bit-level product; the
  datatype-checkpoint build (`build_datatype_checkpoint.sml`) repairs it by
  re-adding the correct *structure-value* `numeralTheory.numeral_mult` family
  to `the_compset`. (`reduceLib.REDUCE_CONV` still stalls on `*` — a separate
  baked compset — so EVAL demos use `computeLib.CBV_CONV`, not `REDUCE`.)
  - **Polymorphic list theory** (`lst = Nil | Cons 'a lst`): `rev(rev l)=l` by
    structural induction (`TypeBasePure.induction_of` → `HO_MATCH_MP_TAC`).
  - **Verified insertion sort** (`insertion_sort_verified.sml`): proves
    `sorted(isort l)` + count-preservation (permutation), then computeLib EVAL
    actually RUNS it (`[3,1,4,1,5,9,2,6]`→sorted, kernel-checked). Reusable
    trick: selective `ASM_ARITH_TAC` (MP_TAC only the pure-numeric assumptions
    before the assumption-blind `ARITH_CONV`).
  - **Verified Euclid GCD** (`gcd_verified.sml`) — NON-STRUCTURAL recursion:
    `gcd` via `tDefine` (`measure SND`, termination by `MOD_LESS`), reasoned via
    the `tDefine`-emitted recursion-induction `gcd_ind`. FULLY CHARACTERISED:
    `gcd_divides` (common divisor) + `gcd_greatest` (universal property — every
    common divisor divides it), both 0-hyp. Idioms: unfold `gcd` ONLY via
    `gcd_0`/`gcd_step` (`CONV_TAC LHS_CONV ONCE_REWRITE` — never `REWRITE_TAC[GCD]`,
    the recursive eqn loops); divides through MOD via `LEFT_SUB_DISTRIB` (truncated
    nat sub distributes unconditionally); close with `FIRST_ASSUM ACCEPT_TAC` not
    ASM_REWRITE-with-a-self-referential-eqn (loops); annotate witnesses `:num`.
  - **Verified compiler** (`verified_compiler.sml`) — the Bahr-Hutton result:
    compile `expr = Const|Plus|Times` to a stack machine (`instr`/`code`/`stack`
    user datatypes), prove `compile_correct: |- !e s. exec (compile e) s =
    SPush (eval e) s` (0-hyp) by expr induction resting on `exec_capp` (exec
    distributes over code concatenation, by code induction). Subtleties: exec's
    underflow catch-alls must CONTINUE (`exec is s`) not short-circuit (`= s`) or
    `exec_capp` is false; exec needs `tDefine` with `measure (code_size o FST)`
    (Define's guesser is defeated by the shape-changing stack); case splits via
    `STRUCT_CASES_TAC` over the TypeBase nchotomy theorems.
  - **Verified merge sort** (`merge_sort_verified.sml`) — a harder sort than
    insertion sort (NON-structural recursion). Tamed with a FUEL parameter so
    the top-level `msort` is structurally recursive (plain Define), with
    `merge`/`split` via `tDefine` (measure on length). Proves BOTH
    `msort_count` (permutation) and `msort_sorted` (sortedness), each 0-hyp,
    then EVALs `[3,1,2,5,4]→[1,2,3,4,5]`. Pitfalls: `merge`'s termination needs
    `pairLib.PAIRED_BETA_CONV` to reduce the paired-lambda measure (FST/SND
    rewrites don't); the selective `ASM_ARITH_TAC` (lift only pure-numeric
    assumptions) recurs here too.
  - **Verified BST** (`verified_bst.sml`) — data-structure verification with an
    INVARIANT: `tree = Leaf | Node tree num tree` with insert/member. Proves
    `member_insert` (membership is correct — insert adds exactly y) and
    `insert_bst : |- !t x. bst t ==> bst (insert x t)` (insert PRESERVES the BST
    ordering invariant), both 0-hyp, by tree induction + COND_CASES + the
    trichotomy facts. Pitfall: STRIP_TAC strips `bst (Node ..)` into the
    assumptions as a FOLDED term (doesn't expand defs) — use `FULL_SIMP_TAC`
    with the defs + the `all_lt_insert`/`all_gt_insert` push-through lemmas, then
    close the residual from the IH by `METIS_TAC[]` (EMPTY set — feeding the
    iff-shaped lemmas to METIS explodes its search).
  - **Verified list-function laws** (`list_laws_verified.sml`, 2026-06-13) — classic
    functional-correctness laws over a USER list datatype (`lst = Nil | Cons 'a lst`),
    each 0-hyp by structural induction: `revacc_correct`/`revacc_reverse`
    (tail-recursive reverse = naive reverse — the accumulator proof), `map_fusion`
    (`lmap f (lmap g l) = lmap (\x. f (g x)) l`, the functor law), `len_append`
    (length is additive), + helpers `append_nil`/`append_assoc`. Idioms: induct via
    `HO_MATCH_MP_TAC (TypeBasePure.induction_of tyi)` then `REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[defs]`; keep the accumulator universally quantified going INTO
    induction (`!l a.`) so the IH is `!a. ...`; `map_fusion`'s Cons case needs
    `BETA_CONV` to reduce the `(\x. f (g x)) h` application; `len_append` stays
    pure-rewrite via `arithmeticTheory.ADD_CLAUSES`. 3-seat fleet (wf_7e7cea22-9fd).
  - **Verified quicksort** (`quicksort_verified.sml`, 2026-06-13) — the third classic sort
    (completes the trio with insertion + merge). Non-structural recursion (recurses on
    `le_filter`/`gt_filter` sublists) via `tDefine` + `measure llen` (termination = the
    filters don't increase length). Proves `qsort_count` (permutation) and `qsort_sorted`
    (sortedness), both 0-hyp, by the tDefine-emitted `qsort_ind` + `sorted_append` + the
    `leall_qsort`/`geall_qsort` bound-preservation lemmas; then computeLib EVAL runs it.
    Idiom: selective `ASM_ARITH_TAC` (lift only assumptions mentioning none of the
    list/predicate constants, so the count/sorted IHs don't poison the arithmetic goal).
    3-seat fleet (wf_c0a81a3c-d0b).
  These proofs were each engineered by a 3-seat ultracode fleet (diverse
  automation: explicit-witness / metis-assisted / simp-assisted); all seats
  verifying independently is the correctness signal, and the most robust (least
  automation) variant is banked. Hand-rolling a datatype num-style
  (`new_type_definition` + recursion theorem + `INDUCT_TAC`, see
  `pair_tydef_milestone.sml`) remains a viable shortcut for specific types.

- **Arithmetic library — DONE** (`/tmp/hol4_arith`, `build_arith_checkpoint.sml`,
  `hol4_arith.rs`, `structure numArith`). `add`/`mult`/`EVEN`/`ODD` defined from
  `num_Axiom` (no Prim_rec), and the Peano laws proved by `INDUCT_TAC` (no
  bool_ss/SAT): `ADD_COMM`, `ADD_ASSOC`, `ADD_RCANCEL`, `ADD_EQ_0`, `MULT_COMM`,
  `RIGHT_ADD_DISTRIB`, and the parity headline `⊢ ∀m n. EVEN (m+n) ⇔ (EVEN m ⇔
  EVEN n)`. This is genuine "real mathematics by induction" on the interpreter.
- **Ordering library — DONE** (`/tmp/hol4_order`, `build_order_checkpoint.sml`,
  `hol4_order.rs`, `structure numOrder`). `LE m n <=> ?p. n = m + p`, then
  `LE_REFL`/`ZERO_LE`/`LE_ADD`/`LE_TRANS`/`SUC_LE`/`LE_ANTISYM` (+ `ADD_LCANCEL`).
  Pitfall: `LE_ANTISYM` must drop one existential-witness assumption before the
  final `ASM_REWRITE_TAC` or it loops into an uncatchable stack overflow.
- **List structural induction — DONE, type AXIOMATIZED** (`list_append_axiomatized.sml`,
  `hol4_list.rs`). `⊢ ∀l. APPEND l NIL = l` and `⊢ ∀l1 l2 l3. APPEND (APPEND l1
  l2) l3 = APPEND l1 (APPEND l2 l3)` by GENUINE `LIST_INDUCT_TAC` (APPEND defined
  from the list recursion theorem). Caveat: the list type + `list_INDUCT`/
  `list_Axiom` are `new_axiom` (labelled `*_AX`) — the derived route is viable
  (`pair_tydef_milestone.sml` shows `new_type_definition` works for parametric
  types) but a volume effort; the general `Datatype` package's remaining work is
  the non-SAT meson/IndDef/ind_type closure (above).

The HOL4 ladder so far (each a `build-hol4-checkpoints.sh` target + an
`#[ignore]` regression test): kernel → theory → parse → bool → tactic → rewrite
→ marker → combin → simp → num → arith → order, plus the **taut** branch off
combin (`/tmp/hol4_taut`: HolSatLib + tautLib via pure-SML DPLL), the **meson**
branch off simp (`/tmp/hol4_meson`: mesonLib first-order proving), and **metis**
off meson (`/tmp/hol4_metis`: metisLib resolution+paramodulation, full bool_ss).
Headline proofs on `/tmp/hol4_simp`: the Drinker Paradox `⊢ ∃x. D x ⇒ ∀y. D y`,
quantifier duality, `S K K = I` (`hol4_fancy.rs`); on `/tmp/hol4_num`: induction
over ℕ + `APPEND_ASSOC` (`hol4_induction.rs`, `hol4_list.rs`); on
`/tmp/hol4_arith`: ADD_COMM/MULT_COMM/EVEN_ADD (`hol4_arith.rs`) + the
**summation mini-development** `hol4_summation.rs` (define `sum`/`osum` via
`num_Axiom`, then **Gauss** `⊢ ∀n. sum n + sum n = mult n (SUC n)` and
**sum-of-odds** `⊢ ∀n. osum n = mult n n` by `INDUCT_TAC` — closed-form
summation identities, no bool_ss/SAT, runs in ~2s on the existing arith
checkpoint); on `/tmp/hol4_order`: the `<=` laws (`hol4_order.rs`); on `/tmp/hol4_taut`:
`⊢ p ∨ ¬p`, De Morgan, Peirce (`hol4_taut.rs`); on `/tmp/hol4_meson`: the drinker
paradox + a symmetric/transitive relation goal by `MESON_TAC` (`hol4_meson.rs`);
on `/tmp/hol4_metis`: `AC_CHAIN` product-reversal + equality congruence by
`METIS_TAC` (`hol4_metis.rs`).

**Pelletier benchmark suite — 46/47 by MESON** (`hol4_pelletier.rs`,
`pelletier_problems.sml`, on `/tmp/hol4_meson`). The classic Pelletier (1986) FOL
benchmark set runs through `MESON_TAC`: 46 of 47 prove (P1–P46, each a verified
0-hyp theorem — incl. P34 Andrews's Challenge, P38, P39 Russell). P47 (Schubert's
Steamroller) is the EXPECTED `MESON_TAC` failure, matching HOL4's own selftest —
so we're at parity with upstream HOL4's MESON on the suite. (Predicates F,S are
alpha-renamed Fp,Sp since F=false / S=combinator in HOL4.)
`theory_dev_proof` remains the kernel-level proof. `tools/closure-probe.sh
/tmp/hol4_theory src/parse` measures parse-layer load on the Theory base.

## Isabelle (the north star) — LOADS, PROVES, does MATH (2026-06-12)

**THE NORTH STAR IS REACHED.** Isabelle's logical Pure runs on the interpreter and
proves real mathematics. The "months away" verdict below (2026-06-06 recon, kept for
history) was wrong by an order of magnitude — the "wall" was three stacked
measurement/stub bugs, not a port. Current state (tests in `crates/polyml-bin/tests/
isabelle_*.rs`, all fenced by `regression.sh full`):
- **Pure logical core LOADS: 261/285** files (kernel + Isar + proof + locale + class +
  specification + simplifier + method + syntax). The remaining 24 are the external/
  system/Scala frontend (message_digest via Scala SHA1, base64/xz/zstd, isabelle_process/
  scala_compiler/build, PIDE document/session, jedit/find_theorems) — genuinely need
  Scala/sockets, not logic. Probe: `tools/isabelle-pure-probe.sh` (per-statement load).
- **Warm checkpoint** `/tmp/isabelle_pure` (`tools/build-isabelle-pure.sh`): exports the
  loaded Pure, reloads in ~2s and PROVES. Reloader's FIRST line must be
  `restore_pure_context ()` (the generic context is thread-local, lost on reload); the
  REPL namespace is Isabelle ML (`out`/`writeln`, NOT `print`).
- **Isabelle PROVES** (`isabelle_proving.rs`): the tactic framework (`Goal.prove` +
  `resolve_tac`/`assume_tac`), the simplifier, theory+axiom development, resolution
  (`RS`), the parser (`Syntax.read_prop`).
- **A first-order OBJECT LOGIC** (`isabelle_object_logic.rs`): built programmatically
  IFOL-style (type `o`, `Trueprop`, connectives, natural-deduction rules as axioms —
  `.thy` loading needs PIDE, so build in ML), proving `A∧B⟹B∧A`, the K/S implication
  axioms, `A∨B⟹B∨A`, `∀`-distribution, `=`-symmetry.
- **PEANO ARITHMETIC by induction** (`isabelle_arithmetic.rs`): `n+0=n`, `add_comm`,
  `add_assoc`, `n*0=0` — the Isabelle analogue of the HOL4 INDUCT_TAC trophies.
- **ℕ IS A COMMUTATIVE SEMIRING** (`isabelle_number_theory.rs`, 2026-06-12, one rung
  up from the above): defines multiplication (recursion on the 1st arg, matching
  `add`) and proves the FULL semiring law set by induction — `add_0_right`/`add_comm`/
  `add_assoc`, `mult_0_right`/`mult_1_right`, `mult_comm`/`mult_assoc`, and BOTH
  distributive laws (`left_distrib`/`right_distrib`) — each a 0-hyp theorem, all in
  ONE driver build (~122M steps, ~3s on the warm checkpoint), gated by `SEMIRING_OK`.
  Real algebra, kernel-checked. The load-bearing subtlety: `mult` lives on an
  EXTENDED theory (one final `ctxtM`/`ctermM`) — every congruence/instantiator on a
  mult-containing goal MUST be built on that same context or you get cross-theory
  cterm mismatches / silent no-op instantiation. `mult_Suc_right` (the RIGHT
  recursion `n*(Suc m)=n+n*m`) is NOT an axiom (mult recurses on its 1st arg) — it is
  proved by induction. Also: the Isabelle ML REPL shadows SML `ref` with
  `Unsynchronized.ref`, so a merged driver wanting a counter must avoid `ref` (use a
  functional fold/andalso). Built by a foundation→fan-out→merge ultracode workflow
  (wf_c761c4e8-236).
- **GAUSS SUMMATION + SUM OF ODDS** (`isabelle_summation.rs`, 2026-06-12, on top of
  the semiring): defines `sum`/`osum` by recursion and proves the two classics by
  induction — **Gauss** `⊢ sum n + sum n = n·(Suc n)` (2·(0+···+n)=n(n+1), doubling
  form) and **sum-of-odds** `⊢ osum n = n·n` (1+3+···+(2n−1)=n²) — each a 0-hyp
  theorem, with a soundness probe (kernel rejects the false "drop +1" Gauss). The
  Isabelle mirror of HOL4 `hol4_summation.rs`. Same extended-theory rule: `sum`/`osum`
  declared on the mult-carrying theory, all cterms routed through one final
  `ctxtS`/`ctermS`. Built by a 3-seat ultracode workflow (wf_4ca14273-6ab) — all
  three seats proved both identities independently.
- **(ℕ, ≤) IS A LINEAR ORDER COMPATIBLE WITH +** (`isabelle_ordering.rs`, 2026-06-12,
  the order rung; mirror of HOL4 `hol4_order.rs`): extends the object logic with TWO
  new logical primitives — the EXISTENTIAL QUANTIFIER (`Ex`/`exI`/`exE`) and PEANO
  DISCRIMINATION (`oFalse`/`oFalse_elim`/`Suc_neq_Zero`/`Suc_inj`) — plus a DISJUNCTION
  connective (`Disj`/`disjI`/`disjE`), defines `m ≤ n ≝ ∃p. n = m+p` (an ML
  abbreviation, not a const — avoids formula-level equality), and proves the full
  order structure by kernel inference, each 0-hyp: `le_refl`/`zero_le`/`le_add`,
  `le_trans` (transitivity), `le_antisym` (⇒ partial order), `le_suc_mono`/
  `le_add_mono` (+ compatibility), `le_total` (linearity ⇒ LINEAR order). Antisymmetry
  rests on `add_left_cancel` + `add_eq_zero_left`, proved by induction via a
  meta-implication→object-predicate REFLECTION (nat_induct's predicate is
  object-level `nat⇒o` and cannot hold a meta `⟹`, so fold the meta-impl into a fresh
  object predicate, induct, unfold; discharge a whole-implication premise with
  `Thm.implies_elim`, NOT `OF`, which resolves on conclusions only). Each new const
  extends the theory — route ALL downstream cterms through ONE final context. Built
  by a foundation→fan-out→merge ultracode workflow (wf_74f3a1e0-a99); the `le_total`
  stretch seat added disjunction itself.
- **DIVISIBILITY: a preorder on ℕ compatible with + and ·** (`isabelle_divisibility.rs`,
  2026-06-12, the number-theory rung above the order; gateway toward GCD/primes):
  defines `a ∣ b ≝ ∃k. b = a·k` (ML abbreviation over the existential) and proves, each
  0-hyp by kernel inference: `dvd_refl`/`one_dvd`/`dvd_zero`, `dvd_trans` (⇒ preorder),
  `dvd_add` (via `left_distrib`), `dvd_mult_right`/`dvd_mult_cong` (· compatibility, via
  `mult_assoc`/`mult_comm`), and the CAPSTONE `dvd_le` (`d∣n ∧ n≠0 ⟹ d ≤ n`, tying
  divisibility to the linear order — uses a num-cases lemma + `mult_Suc_right` + the
  discrimination axiom, with n≠0 supplied as a meta-implication `oeq n 0 ⟹ oFalse`).
  Built by a foundation→fan-out→merge ultracode workflow (wf_2eb4085c-828). NOTE: SML's
  comment lexer NESTS — a literal `(* ... *)` fragment inside a comment (e.g. writing
  "(· compatibility)" with an ASCII open-paren-star) reads as an unterminated nested
  comment ("end of file found in comment"); avoid stray `(*`/`*)` in driver comments.
- **THE EUCLIDEAN ALGORITHM — gcd universal property + BÉZOUT + MODULAR INVERSE**
  (`isabelle_gcd.rs`, `isabelle_gcd.sml`, 2026-06-15). Closes the gap the rest of the tower
  deliberately sidestepped ("gcd/Bézout needs integers over ℕ"): all four results are proved
  as PURE EXISTENTIALS over the existing theory (NO new constant, NO new axiom), by genuine
  kernel inference, driven by the already-proved division theorem (`div_mod_exists`) through
  `strong_induct`. `gcd_props` (`⊢ ∀a b. ∃g. g∣a ∧ g∣b ∧ ∀d. d∣a ⟹ d∣b ⟹ d∣g` — the gcd
  VALUE + its universal property, by strong induction on b: g=a at b=0, else a=b·q+r with r<b,
  IH at (b,r), `dvd_diff` for the greatest claim); `bezout` (same + `∃x y. a·x=b·y+g ∨
  b·y=a·x+g` — Bézout in the two-sided ℕ form, no subtraction, the coefficients tracked
  through the same induction); `coprime_bezout` (coprimality forces g=1); and the stretch
  `mod_inverse` (`⊢ prime p ⟹ ¬(p∣a) ⟹ ∃b. cong p (a·b) 1`). Each carries a soundness probe.
  KEY de-risking insight: because `div_mod_exists` is itself existential, gcd/Bézout need no
  `mod`/`div` FUNCTION and hence no theory extension — sidestepping the context-routing /
  varify machinery that dominates the rest of the tower. Built on the unified base via the new
  `common::with_ntbase` (second-tier consolidation: helpers + ntbase, no re-embedding); proved
  by a 3-phase multi-seat ultracode fleet (wf_a420c57e-d18: gcd-props → bezout →
  coprime/inverse), re-verified end-to-end by hand. The earlier Euclid's-lemma note that gcd/
  Bézout "needs integers over ℕ" / "is entirely avoidable" stands as written for THAT proof
  (the Gauss descent genuinely avoids them) — but gcd + Bézout are now available over ℕ
  directly should later work (Wilson, CRT, Euler) want them.
- **THE CHINESE REMAINDER THEOREM** (`isabelle_crt.rs`, `isabelle_crt.sml`, 2026-06-15 — the
  first payoff of the gcd/Bézout/inverse machinery). For coprime moduli m,n and any residues
  a,b there is an x ≡ a (mod m) and ≡ b (mod n), unique mod m·n — both halves, by genuine
  kernel inference over ℕ (two-sided cong, no subtraction). `gen_inverse` (general modular
  inverse for coprimes, `coprime a m ⟹ 0<m ⟹ ∃b. cong m (a·b) 1`, from `coprime_bezout`, both
  Bézout disjuncts handled — the −1 case uses the square trick a·(x·a·x) ≡ (−1)² = 1);
  `crt_exists` (EXISTENCE, by the construction `x = a·(n·s) + b·(m·t)` with n·s≡1 mod m and
  m·t≡1 mod n, via `cong_add`/`cong_mult`/`cong_refl`); `gauss` (`coprime n m ⟹ n∣m·c ⟹ n∣c`,
  from `coprime_bezout` + `dvd_diff`); `coprime_mult_dvd` (`coprime m n ⟹ m∣k ⟹ n∣k ⟹ m·n∣k`,
  via gauss); and `crt_unique` (UNIQUENESS: two solutions agree mod m·n). Built on the full
  gcd development via the new `common::with_gcd` (third consolidation tier: helpers + ntbase +
  isabelle_gcd, no re-embedding). Each lemma has a soundness probe. Proved by a 3-phase
  multi-seat ultracode fleet (wf_f77ae210-0f5: gen-inverse → crt-existence → crt-uniqueness),
  re-verified end-to-end by hand. Next reachable with this machinery: Wilson's theorem and
  Euler's theorem (both need a finite-product/pairing argument over a residue range, the one
  piece the tower still lacks).
- **CLASSIC COMBINATORIAL IDENTITIES** (`isabelle_combinatorics.rs`, `isabelle_combinatorics.sml`,
  2026-06-15 — a combinatorics flavour on the binomial-theorem machinery). Three famous
  binomial-coefficient identities, each 0-hyp by kernel inference on top of the binom_thm
  development (binom + Pascal `binom_Suc_Suc`, the higher-order finite sum `sumf`, the
  sum-algebra `sum_cong`/`sum_add`/`sum_mult_l`/`sum_peel_first`, `pow`): `pascal_row_sum`
  (`∑_{k=0}^n C(n,k) = 2^n`, the Pascal-triangle row sum — proved the slick way, as a COROLLARY
  of `binom_theorem` at a=b=1, with `pow_one_base` collapsing 1^k and `sum_cong` tidying the
  summand); `hockey_stick` (`∑_{i=0}^n C(i,r) = C(n+1,r+1)`, induction on n + Pascal); and the
  capstone `vandermonde` (`∑_{j=0}^k C(m,j)·C(n,k−j) = C(m+n,k)`, the classic Pascal-split +
  reindex + recombine induction, with truncated `sub`). Each has a soundness probe. Built via
  the new `common::with_binom_thm` (a sibling consolidation tier: classical foundation +
  isabelle_binom_thm). Proved by a multi-seat ultracode fleet racing all three concurrently
  (wf_bd77c82b-594, all three landed including Vandermonde); re-verified end-to-end by hand.
  Gotcha logged: `varify` ETA-CONTRACTS a summand lambda (`%k. binom n k` → `binom n`), so the
  intended-statement aconv probe must compare against the eta-contracted form.
- **CLOSED-FORM SUMMATION THEOREMS** (`isabelle_summation_forms.rs`, `isabelle_summation_forms.sml`,
  2026-06-15 — named polynomial closed forms over the higher-order `sumf`). Three classics, each
  0-hyp by nat induction + the semiring algebra (pure identities, no new constant; sums cleared of
  denominators to stay in ℕ): `nicomachus` (`∑_{k=0}^n k³ = (∑_{k=0}^n k)²`, Nicomachus's theorem,
  via the Gauss-doubling helper `gauss2`: `2·∑k = n(n+1)`); `faulhaber_sq` (`6·∑k² = n(n+1)(2n+1)`,
  Faulhaber's sum of squares); `pronic_sum` (`3·∑k(k+1) = n(n+1)(n+2)`). Each has a soundness probe.
  Built on isabelle_binom_thm.sml via `common::with_binom_thm`. Proved by a multi-seat ultracode
  fleet racing all three (wf_62507100-db8); re-verified end-to-end by hand. (NB: distinct from the
  older `isabelle_summation.sml`, which proved Gauss + sum-of-odds via a first-order `sum`/`num_Axiom`
  rather than the higher-order `sumf`.)
- **THE FINITE-PRODUCT COMBINATOR `prodf`** (`isabelle_prodf.rs`, `isabelle_prodf.sml`,
  2026-06-15 — the multiplicative mirror of `sumf`, the structural piece toward Wilson/Euler).
  A NEW higher-order constant `prodf : (nat⇒nat)⇒nat⇒nat` defined conservatively by two asserted
  recursion axioms (exactly as `sumf`/`fact`/`pow`): `prodf f 0 = f 0`, `prodf f (Suc n) =
  (prodf f n)·(f (Suc n))`. Core algebra proved 0-hyp by kernel induction: `prod_cong`
  (`(∀k≤n. f k = g k) ⟹ prodf f n = prodf g n`, mirrors `sum_cong`), `prod_const_pow`
  (`prodf (λk. c) n = pow c (Suc n)`, with an exponent soundness probe), `prod_mult_combine`
  (`(prodf f n)·(prodf g n) = prodf (λk. f k·g k) n`, mirrors `sum_add`). Adding the const
  EXTENDS the theory, so the development builds ONE final context (`ctxtPr`/`ctermPr` over a
  `thyPr` extending the base `thySub`) and RE-VARIFIES every reused base lemma onto it before
  instantiating — the standard new-const discipline; the proof is a clean template for mirroring
  any `sumf` lemma to `prodf`. Built on `isabelle_binom_thm.sml` (the sumf template) via
  `common::with_binom_thm`. Proved by a 3-seat ultracode fleet (wf_66aae28d-292); re-verified by
  hand. **Remaining for Wilson/Euler: a product-permutation/pairing-invariance lemma for `prodf`
  (product unchanged under reindexing by an involution/bijection) — the genuinely hard piece.**
- **THE MULTIPLICATIVE GROUP MOD p — the Wilson keystones** (`isabelle_mult_group.rs`,
  `isabelle_mult_group.sml`, 2026-06-15). The algebraic core of (ℤ/pℤ)*, each 0-hyp by kernel
  inference over the two-sided `cong`: `inverse_unique` (`cong p (a·b) 1 ⟹ cong p (a·c) 1 ⟹
  cong p b c`, modular inverse is unique — a pure congruence chain b ≡ b·1 ≡ b·(a·c) = (a·b)·c
  ≡ 1·c ≡ c, no primality); `mod_cancel` (`prime p ⟹ ¬(p∣a) ⟹ cong p (a·b) (a·c) ⟹ cong p b c`,
  cancellation by a unit, via Euclid's lemma + monotonicity); and `lagrange_roots` — **Lagrange's
  theorem on square roots of unity**: `prime p ⟹ cong p (a·a) 1 ⟹ (cong p a 1 ∨ cong p (Suc a) 0)`
  (the only square roots of 1 mod a prime are ±1; −1 written as `Suc a ≡ 0` to avoid truncated
  subtraction; via the identity `(a−1)(a+1) = a²−1` + Euclid's lemma). Each has a soundness probe.
  Built on the gcd/Bézout/Euclid-lemma development via `common::with_gcd`. Proved by a multi-seat
  ultracode fleet (wf_3eef19b5-87f); re-verified by hand. CAPTURE GOTCHA logged: when building an
  `oeq_subst` predicate `%z. cong p X z`, use `Term.lambda` over a FRESH Free, NOT `Abs(...,Bound 0)`
  — the `cong` constructor inserts its own inner existential `Abs`, so a literal `Bound 0` gets
  captured by that inner k-binder (\"OF: no unifiers\"). These three are the algebraic heart of
  Wilson's theorem; full Wilson still needs `prodf` merged onto this modular base + the
  product-pairing lemma.
- **THE CENTRAL BINOMIAL COEFFICIENT IDENTITY** (`isabelle_central_binomial.rs`,
  `isabelle_central_binomial.sml`, 2026-06-15 — a Vandermonde payoff). `binom_symmetry`
  (`∀n k. k≤n ⟹ C(n,k) = C(n,n−k)`, by nat induction with k object-universally quantified so the
  IH applies at both k and Suc k, + Pascal + a `sub` case-split; needs a `sub_Suc`-style lemma and
  `le_Suc_Suc_rev`) and `central_binomial` (`∑_{k=0}^n C(n,k)² = C(2n,n)`, the central binomial
  coefficient) — the latter a short COROLLARY of `vandermonde` instantiated at m=n,k=n
  (`∑_j C(n,j)·C(n,n−j) = C(2n,n)`) with the summand rewritten by `binom_symmetry` under `sum_cong`.
  Both 0-hyp with soundness probes. Built on `isabelle_combinatorics.sml` (carries Vandermonde) via
  the new `common::with_combinatorics`. Proved by a 2-phase ultracode fleet (wf_f6d7e8db-f16);
  re-verified by hand.
- **THE INVOLUTION-PAIRING LEMMA — the historic Wilson wall, BROKEN** (`isabelle_wilson_pairing.rs`,
  `isabelle_wilson_pairing.sml`, 2026-06-15). The classical Wilson proof pairs each residue with
  its inverse; formalizing that pairing — **a product invariant under a fixed-point-free
  involution, with no finite-set library** — has been the obstruction. Now proved by genuine kernel
  inference in two parts. (1) **A list-product library** on the modular base: a `natlist` datatype
  (defined here, `lnil`/`lcons` + `list_induct`) with `lprod`/`lmem`/`lremove` (remove-first, via
  conditional axioms)/`llen`/`lnodup`, and the lemmas the pairing needs — the KEY one being
  `extract : lmem x L ⟹ lprod L = x · lprod (lremove x L)` — plus `mem_remove`, `llen_remove`
  (removal strictly shortens), `nodup_remove`, each 0-hyp by list induction (`LIST_LIB_OK`).
  (2) **`pairing_lemma`**: for a list `L` and function `inv`, `lnodup L ⟹ (∀x∈L. inv x ∈ L) ⟹
  (∀x∈L. cong p (x·inv x) 1) ⟹ (∀x∈L. inv x ≠ x) ⟹ (∀x∈L. inv(inv x)=x) ⟹ cong p (lprod L) 1`,
  by STRONG INDUCTION on `llen L` (extract head `a` and its partner `inv a` from the tail, remove
  both, recurse — `inv` injective on `L` from the involution makes the residual list still closed)
  (`PAIRING_OK`). Soundness probes confirm it genuinely uses the inverse hypothesis and is
  conditional. Built on the modular/keystone base via the new `common::with_mult_group`. Proved by
  a 2-phase ultracode fleet (wf_1ef6ffe6-859, ~97 min — Phase 1 list lib, Phase 2 the wall); each
  re-verified end-to-end by hand. KEY gotchas logged: conditional-function axioms return the
  premise STILL attached (implies_elim against the assumed condition before use); disjE case-arms
  must be META-implications, not impI-wrapped object implications; object `neg A = Imp A oFalse` is
  discharged with `mp`, not `implies_elim`. **NEXT toward full Wilson:** construct the list `[2..p-2]`
  / `[1..p-1]` and prove it closed under the modular inverse (the residue-range construction), then
  assemble `(p-1)! = 1·∏[2..p-2]·(p-1) ≡ -1`. **Euler's theorem reuses `pairing_lemma` directly.**
- **THE MODULAR-INVERSE FUNCTION + RESIDUE RANGE** (`isabelle_wilson_inverse.rs`,
  `isabelle_wilson_inverse.sml`, 2026-06-15 — the second Wilson-finale piece). The `pairing_lemma`
  needs the modular inverse as a literal involution FUNCTION, but the object logic has no choice
  operator and `cong` is not directly decidable. THE UNLOCK: define a `mod` function (rmod/rdiv via
  conservative axioms from the division theorem) so congruence becomes DECIDABLE EQUALITY —
  `cong_iff_rmod : 0<p ⟹ (cong p a b ⟺ rmod a p = rmod b p)` (both directions) — then the inverse
  is built by a list SEARCH over the residue range. Defined `upto n = [1..n]` (with `lnodup`,
  `lmem_upto`) and `finv p x` (search `upto(p-1)` for x's inverse), proved for prime p and x in
  [1..p-1]: `finv_inv` (cong p (x·finv p x) 1), `finv_mem` (in range), `finv_invol` (`finv p (finv
  p x) = x` LITERAL involution, via `inverse_unique`), `finv_neq` (fixed-point free on [2..p-2], via
  `lagrange_roots`) — exactly `pairing_lemma`'s hypotheses. Each 0-hyp, aconv intended, probed.
  Built via `common::with_wilson_pairing`. Proved by a 2-phase ultracode fleet (wf_a22d8bd7-115,
  ~106 min); re-verified by hand. NEXT (the finale): apply `pairing_lemma` to [2..p-2] with `finv`
  ⟹ `lprod[2..p-2] ≡ 1`, then `(p-1)! = 1·lprod[2..p-2]·(p-1) ≡ -1` — Wilson's theorem.
- **WILSON'S THEOREM** (`isabelle_wilson.rs`, `isabelle_wilson.sml`, 2026-06-15 — A SUMMIT REACHED):
  `⊢ prime p ⟹ (p−1)! ≡ −1 (mod p)` (`cong p (lprod (upto (p−1))) (p−1)`), a 0-hyp theorem by
  genuine LCF kernel inference on the Rust interpreter — the classical companion to Fermat's little
  theorem. Proved by the inverse-pairing argument: each residue in [2..p−2] is paired with its
  modular inverse `finv` (1 and p−1 are self-inverse, `finv_one`/`finv_pm1`), [2..p−2] is closed
  under `finv` / fixed-point-free / an involution, so by the **involution-pairing lemma**
  `lprod[2..p−2] ≡ 1`, whence `(p−1)! = (p−1)·1·∏[2..p−2] ≡ p−1 ≡ −1`. The whole campaign was FOUR
  ultracode fleet runs (~6.5 hrs total): the Wilson keystones (`isabelle_mult_group`) → the
  list-product library + **the involution-pairing lemma, the historic wall** (`isabelle_wilson_pairing`)
  → the **mod function + decidable congruence + the modular-inverse FUNCTION** (`isabelle_wilson_inverse`)
  → the **assembly** (`isabelle_wilson`, wf_39658abf-b42). Each layer re-verified by hand and committed.
  **SOUNDNESS NOTE (audited):** the statement uses `prime2` = the GENUINE structural prime
  (1<p ∧ ∀d. d∣p ⟹ d=1∨d=p), used consistently by the entire keystone chain (euclid_lemma /
  mod_inverse / lagrange_roots all take prime2; 107 prime2 uses, 0 of the legacy `prime`/primePredAbs
  downstream). The legacy `prime` (phase-2 `primePredAbs`) has a de-Bruijn capture bug — its raw
  `Bound 0` is captured by `dvd`'s inner existential — so it is **dead/unused**; ALWAYS use `prime2`.
  Three soundness probes on the result pass (needs the prime hyp; residue is p−1 not 0; not the false
  `≡1`). **Euler's theorem is the next summit and reuses `pairing_lemma` + `finv` directly** (product
  over the reduced residues, x↦a·x permutes them).
- **EULER'S THEOREM** (`isabelle_euler.rs`, `isabelle_euler.sml`, 2026-06-16 — the summit
  predicted above, the generalisation of Fermat's little theorem to a composite modulus):
  `⊢ 1<n ⟹ unit_test n a ⟹ cong n (pow a (phiU n)) 1` — i.e. **a^φ(n) ≡ 1 (mod n)** for a a
  unit mod n, a 0-hyp LCF kernel theorem (only classical assumption = `ex_middle`; axiom audit
  clean — all 74 axioms are the established conservative foundation). THE DESIGN UNLOCK:
  coprimality is defined AS invertibility — `unit_test n r = searchCond n r (finv n r)` (the
  inverse-search succeeds) — so "is a unit" and "has an inverse" coincide BY CONSTRUCTION
  (`unit_has_inv` / `inv_imp_unit`), closing the gap the earlier gcd-based run hit (coprime via
  gcd with no bridge to inverse-existence). Proof = Lagrange in the unit group: Phase 1 (25
  sub-lemmas, `EULER_BIJ_OK`) builds the unit group + the **multiply-by-a bijection** on the
  reduced residues (`urrl`/`phiU`, the units; `f r = rmod(a·r)n` is closed/injective/surjective,
  so `bij_prod : lprod(map f (urrl n)) = lprod(urrl n)` via the derived permutation-invariance
  lemma `lprod_perm`); Phase 2 factors `lprod(map (mult a) U) = a^|U|·lprod U` (`prod_map_factor`),
  bridges the rmod-map to the plain map (`rmod_bridge`), and cancels the unit product `U`
  (`prod_unit` + `gen_cancel`) to get a^φ(n)·U ≡ U ⟹ a^φ(n) ≡ 1. Four soundness probes pass
  (aconv intended; needs `unit_test`; exponent is φ(n) not n; residue is 1). Built by a 6-agent
  multi-phase ultracode fleet (wf_72da364c-704, ~2.3h); **re-verified end-to-end by hand**
  (3,269,745,139 steps, Result: Tagged(0), 145 OK markers, zero exceptions). CAVEAT: the driver
  is currently SELF-CONTAINED (embeds its own foundation, re-asserting gcdf/rfilter/rrl), so it
  is run DIRECTLY (no `with_*` splice), like isabelle_modular/power/fta_unique — consolidating it
  onto `with_wilson_inverse` + isabelle_euler_foundations.sml is a tracked follow-up. With Wilson,
  FLT, Euclid, √2, FTA, CRT, this rounds out the landmark theorems of elementary number theory on
  the Rust interpreter.
- **EULER'S CRITERION (±1 dichotomy + QR-forward)** (`isabelle_euler_criterion.rs`,
  `isabelle_euler_criterion.sml`, 2026-06-16): for an ODD prime p (p−1 = 2m) coprime to a,
  **`a^((p−1)/2) ≡ ±1 (mod p)`** — `⊢ prime2 p ⟹ ¬(dvd p a) ⟹ oeq (sub p 1)(add m m) ⟹
  Disj (cong p (pow a m) 1) (cong p (Suc (pow a m)) 0)` (−1 as `Suc(a^m)≡0` to dodge truncated ℕ
  sub) — plus **QR-forward** `(∃x. cong p (mult x x) a) ⟹ cong p (pow a m) 1` (a quadratic residue
  forces +1). Both 0-hyp; only classical assumption = `ex_middle`; 38-axiom audit clean (no axiom
  mentions cong/criterion/lagrange). Proof: y=a^m, y·y = a^(m+m) = a^(p−1) ≡ 1 (Fermat-for-units
  `apm1`), so `lagrange_roots` (only sqrt of 1 mod a prime are ±1) ⟹ y≡1 ∨ y≡−1. THE
  BASE-COMPOSITION UNLOCK: Fermat (isabelle_flt) and `lagrange_roots` (isabelle_mult_group) live in
  different branches; the foundation re-derives `mod_cancel`+`lagrange_roots` on the **flt base**
  (both euclid_lemma-based, lighter than euler's 3.3B-step base) so Fermat-power-algebra + lagrange +
  pow/cong coexist in one context. Built by a foundation→3-seat→verify ultracode fleet
  (wf_0415115b-1a5, all 3 seats proved dichotomy+QR-forward); **re-verified by hand** (2,184,717,059
  steps, Tagged(0), all EC_*_OK + PROBE_OK markers, zero exceptions). **NOT proved: the REVERSE
  (a^m≡1 ⟹ a is a QR), the harder half of the full iff — needs a primitive-root/roots-counting
  argument** (the gateway toward quadratic reciprocity). Self-contained driver (run directly).
- **WILSON'S CONVERSE** (`isabelle_wilson_converse.rs`, `isabelle_wilson_converse.sml`,
  2026-06-16): `⊢ composite n ⟹ 4 < n ⟹ dvd n (factorial n)` — every composite n>4 divides
  (n−1)! (so (n−1)! ≡ 0, not −1, mod n). With Wilson's theorem this is the non-trivial half of
  the primality characterization **n prime ⟺ (n−1)! ≡ −1 (mod n)** (the n=4 exception, 3!=6≡2,
  is excluded by 4<n). A 0-hyp theorem that adds **NO new axioms** (the delta is purely derived
  over the base; only classical assumption = the base's single `ex_middle`). ELEMENTARY proof
  (does NOT use Wilson's theorem): a composite has a proper divisor a with cofactor b (n=a·b),
  both in [1..n−1]; KEY LEMMA = two DISTINCT list members x≠y ⟹ `dvd (mult x y) (lprod L)` (via
  `extract` twice); perfect-square case n=a² uses a and 2a (distinct, both <n iff n>4). FIRST
  CLEAN SPLICE in the recent summits: built on `common::with_wilson_inverse` (has lprod/upto/
  extract/lremove/dvd), so it banks as a small ~668-line DELTA (not a self-contained monolith
  like euler/criterion). foundation→3-seat→verify ultracode fleet (wf_cf5755d5-b5f, all 3 seats
  incl. the square case); re-verified by hand through the real splice. LEFT: the small cases
  (n=2,3,4) + a single combined-iff wrapper theorem — this proves the dvd-the-factorial heart.
- **−1 IS A QUADRATIC RESIDUE mod p for p ≡ 1 (mod 4)** (`isabelle_neg1_qr.rs`,
  `isabelle_neg1_qr.sml`, 2026-06-16 — the Lagrange / First Supplement to Quadratic Reciprocity,
  easy direction; the GATEWAY to Fermat's two-square theorem): `⊢ prime2 p ⟹ (p−1=4k) ⟹
  ∃x. cong p (x·x) (p−1)` (and the explicit `wsq : cong p (w·w) (p−1)` with w = ((p−1)/2)!), i.e.
  for a prime p≡1 mod4, `((p−1)/2)!` is a square root of −1 (≡ p−1) mod p. Both 0-hyp; only
  classical assumption = `ex_middle`. Proof: m=(p−1)/2 even; **Wilson** (the PROVEN `wilson`, not
  re-axiomatized) gives (p−1)! ≡ −1; pairing j with p−j gives (p−1)! ≡ (−1)^m·(m!)², and m even
  kills the sign ⟹ (m!)²≡−1. THE CRUX was the parity-of-product lemma — cracked via the **pair-up**
  route (`parity_crux`: each pair (p−a)(p−b) ≡ a·b cancels its own signs, NO (−1)^m). Adds
  `common::with_wilson` (Wilson's theorem on the modular-inverse base) so it banks as a clean
  ~1146-line delta. foundation→3-seat→verify ultracode fleet (wf_a1850dba-804; all 3 seats, two
  independent routes — pair-up + signed — converging with a p=5 numeric cross-check); re-verified
  by hand (60-axiom audit clean: only the conservative foundation + `ex_middle` + the conservative
  `uprod` recursion; Wilson is the proven theorem; probes confirm it needs prime + p≡1mod4 and the
  residue is p−1=−1 not 0). LEFT: the converse (p≡3mod4 ⟹ −1 NOT a QR), and piece B of two-square
  — Thue's pigeonhole descent (`x²≡−1` ⟹ `p=a²+b²`), which needed finite-counting machinery the
  tower lacked — **NOW BUILT** (see THUE'S LEMMA below).
- **THUE'S LEMMA** (`isabelle_thue.rs`, `isabelle_thue.sml`, 2026-06-17 — the pigeonhole gateway to
  Fermat's two-square theorem): `⊢ 0<p ⟹ ∃s x1 x2 y1 y2. (s²≤p ∧ p<(s+1)²) ∧ x1≤s ∧ x2≤s ∧ y1≤s ∧
  y2≤s ∧ ¬(x1=x2 ∧ y1=y2) ∧ cong p (x1 + a·y2) (x2 + a·y1)` — for the given a there are two DISTINCT
  points in the [0..s]² grid (s=⌊√p⌋) whose `i + a·(s−j)` residues collide mod p (the ℕ-friendly,
  subtraction-free collision form: X=x1−x2, Y=y1−y2 give X≡a·Y, |X|,|Y|≤s<√p, not both 0). 0-hyp;
  only classical assumption = `ex_middle`. Required NEW machinery the tower lacked, all kernel-proved:
  **`floor_sqrt`** (integer √, `∃s. s²≤n<(s+1)²` by induction), a list **`list_pigeonhole`**, a
  `[0..m−1]` range list, and the crux **image-collision pigeonhole** (`dup_gridres`) — proved
  DIRECTLY for the concrete residue recursion (NOT an axiomatized `Free f`, which would be unsound)
  by the "minus-one-value" induction. Built on `common::with_wilson_pairing` (`cong` + the `natlist`
  lib, without the heavy Wilson theorem) by TWO ultracode fleets: wf_010172c9-d24 built the infra +
  bridge + `collision_exists` (the residue list has a duplicate); wf_67a27224-97d closed the
  image-collision pigeonhole + packaged the existential (all 3 seats, two routes). Re-verified by hand
  (byte-identical re-derivation, Tagged(0), 55-axiom audit clean, aconv + 0-hyp + distinctness/
  non-degeneracy probes; a fleet caught + corrected a latent `rearrange` bug → `rearrange2`). NEXT
  (the dream): Fermat two-square — instantiate Thue at an a with a²≡−1 (banked: `isabelle_neg1_qr` for
  p≡1 mod4), giving u²+v²≡0 mod p with 0<u²+v²<2p ⟹ p=u²+v². Reachable on `with_wilson` (extends this
  base with Wilson's theorem) + the banked neg1_qr; the hard combinatorial core (the pigeonhole) is done.
- **FERMAT'S TWO-SQUARE THEOREM** (`isabelle_twosquare.rs`, `isabelle_twosquare.sml`, 2026-06-17
  — A CROWN JEWEL): `⊢ prime2 p ⟹ (p−1 = 4k) ⟹ ∃a b. p = a²+b²` — every prime p ≡ 1 (mod 4) is a
  sum of two squares (13=2²+3², 29=2²+5², …), a landmark of elementary number theory, machine-checked
  on the self-bootstrapped Rust PolyML interpreter. 0-hyp over the GENUINE structural prime; only
  classical assumption = `ex_middle`. The classical proof, assembled from the banked cores: Wilson ⟹
  `((p−1)/2)!² ≡ −1` so −1 is a QR (`isabelle_neg1_qr`); **Thue's lemma** (`isabelle_thue`) ⟹ a
  nontrivial collision `x₁+c·y₂ ≡ x₂+c·y₁`; the descent U=|x₁−x₂|, V=|y₁−y₂| give `U²≡c²V²≡−V²` so
  `p∣U²+V²`, and with `0<U²+V²<2p` (needs "a prime is not a perfect square", `not_square`) the only
  multiple of p in range forces `U²+V²=p`. Built by a foundation→2-seat→verify ultracode fleet
  (wf_737ad703-71d; both seats proved it independently, identical conservative 67-axiom base). The
  driver is SELF-CONTAINED (embeds the full Wilson+QR+Thue chain with one clashing axiom renamed
  during the splice → `rmod_lt_th`), run directly. Re-verified by hand (Tagged(0), aconv + 0-hyp;
  soundness probes confirm it needs the prime hyp + p≡1mod4 and the conclusion is genuinely a SUM of
  two squares; Thue/QR/Wilson are USED as proven lemmas, residue stays concrete). The campaign was
  THREE fleets: Thue infra+bridge → close the image-collision pigeonhole → the two-square descent.
- **STRONG INDUCTION + STRICT LINEAR ORDER + PRIMALITY** (`isabelle_primes.rs`,
  2026-06-12, the top of the ladder). FULLY GENUINE (0-hyp, pure kernel, no axioms
  beyond the ladder's Peano/discrimination set): **`strong_induct`** — course-of-values
  induction DERIVED from `nat_induct` + the strict order (`(⋀n.(⋀m. m<n ⟹ P m)⟹P n)⟹⋀n.P n`),
  the headline; `lt_trans`/`lt_trichotomy` (the strict linear order, `m<n ≝ Suc m ≤ n`);
  `prime_two` (`⊢ prime 2`, STRUCTURAL `prime p ≝ 1<p ∧ ∀d. d∣p ⟹ d=1∨d=p`); `prime_gt_1`.
  CAPSTONE WITH A DISCLOSED ASSUMPTION: `prime_divisor_exists` (`2≤n ⟹ ∃p. prime p ∧ p∣n`,
  "every n≥2 has a prime divisor") is proved BY strong induction + `dvd_trans` chaining —
  genuine structure — but RESTS ON a classical axiom `prime_cases` (`1<n ⟹ prime n ∨ ∃d.
  1<d<n ∧ d∣n`) over an ABSTRACT `prime` const (not the structural one). Pure here is
  intuitionistic (no excluded middle), so the case-split cannot be derived; in real
  Isabelle/HOL it is a lemma from EM + the definition + `dvd_le`. So the capstone is "every
  n≥2 has a prime divisor MODULO the classical primality case-split", a demonstration that
  the strong-induction machinery reaches it — NOT a from-first-principles proof. Principled
  follow-up: add ONE excluded-middle axiom and DERIVE `prime_cases` from the structural
  `prime` + `dvd_le`, unifying the two `prime`s. Built by a foundation→fan-out→merge
  ultracode workflow (wf_968ad1d0-b77). **NOTE: the caveated capstone here is now
  SUPERSEDED by `isabelle_classical_primes.rs` (below), which derives `prime_cases`
  genuinely.**
- **CLASSICAL FOL + the GENUINE prime-divisor theorem** (`isabelle_classical_primes.rs`,
  2026-06-13 — the honest completion). Makes the object logic CLASSICAL: adds object
  `Imp`/`Conj`/`Forall` + ONE classical axiom, EXCLUDED MIDDLE (`⊢ A ∨ ¬A`), and DERIVES
  the standard classical lemmas (each 0-extra-hyp, aconv-checked): `dbl_neg` (¬¬A⟹A),
  `deMorgan_or`, `not_imp` (¬(A⟶B)⟹A∧¬B), `not_forall` (¬∀⟹∃¬). Then — the key — DERIVES
  the primality case-split `prime_cases` (`1<n ⟹ prime n ∨ ∃d. 1<d<n ∧ d∣n`) from EM +
  the STRUCTURAL `prime` + `dvd_le` + the classical lemmas (NOT an axiom this time), and
  proves the GENUINE capstone `prime_divisor_exists` (`2≤n ⟹ ∃p. prime p ∧ p∣n`, structural
  prime) BY strong induction. The only classical assumption is excluded middle (which real
  Isabelle/HOL object logics have) — soundness probes confirm the kernel rejects false
  variants. This closes the honesty gap from `isabelle_primes.rs`: a real, named
  number-theory theorem proved from a single classical axiom on our Rust runtime. Built by
  a 4-phase ultracode pipeline (wf_26188260-4af): classical FOL → NT connectors + strong
  induction → prime_cases (3 seats all derived it) → capstone (2 seats both proved it).
- **EUCLID'S THEOREM — the infinitude of primes** (`isabelle_euclid.rs`, 2026-06-13 — the
  GRAND CAPSTONE, top of the ladder): `⊢ ∀n. ∃p. prime p ∧ n < p` — for every n there is a
  prime greater than n. A 0-hyp theorem over the STRUCTURAL prime, genuine kernel inference,
  only classical assumption = excluded middle. Proof: given n, N = n!+1 ≥ 2 (`fact_pos`) has
  a prime divisor p (the genuine `prime_divisor_exists`); if p ≤ n then p∣n! (`dvd_fact`) and
  p∣(n!+1), contradicting consecutive-coprimality (`consec_coprime`: a prime can't divide
  two consecutive numbers); so p > n. Helpers: a real recursive `fact` const + `fact_pos`,
  `dvd_fact`, `mult_le_mono`, `mult_eq_one`, `le_cases`, `dvd_self_mult`. Built on
  `isabelle_classical_primes.sml` by a 3-phase ultracode pipeline (wf_a72a4b68-c26): helpers
  → consec_coprime (3 seats all derived it) → Euclid (2 seats both proved it). The full
  self-derived Isabelle number theory now runs: object logic → Peano → semiring → summation
  → order → divisibility → strong induction → classical FOL → genuine prime-divisor →
  **Euclid's theorem**, all on the Rust PolyML interpreter.
- **INFINITELY MANY PRIMES ≡ 3 (mod 4)** (`isabelle_primes_3mod4.rs`,
  `isabelle_primes_3mod4.sml`, 2026-06-16 — the classical baby case of Dirichlet's theorem on
  primes in arithmetic progressions, one rung above Euclid): `⊢ ∀n. ∃q. prime2 q ∧ n < q ∧
  q ≡ 3 (mod 4)` (mod-4 encoded additively as `∃t. q = 4·t + 3`; n<q is genuine strict order).
  0-hyp, only classical assumption = `ex_middle`. Euclid-style: N = 4·n!−1 = 4·(n!−1)+3 ≡ 3 mod4,
  N>1; the KEY LEMMA (strong induction) — a number ≡3 mod4 with m>1 has a prime factor ≡3 mod4,
  because a product of `≡1`-factors stays `≡1` (`mul_r3_split`) — gives a prime q≡3 mod4 dividing
  N; q>n via `dvd_fact` + `consec_coprime` (q≤n ⟹ q∣n! ∧ q∣4n!=N+1 ⟹ q∣1). Built on the new
  `common::with_euclid` splice (the factorial / `dvd_fact` / `consec_coprime` machinery on the
  classical-primes foundation) by a foundation→3-seat→verify ultracode fleet (wf_e8b99c4e-d3e,
  all 3 seats); re-verified by hand (1.18B steps, Tagged(0), 30-axiom audit clean, 3 soundness
  probes confirming the n<q orientation + mod-4 + primality conjuncts are genuinely present).
  Scope: the elementary 3-mod-4 case only (the ≡1-mod-4 companion needs −1-is-a-QR, beyond
  Euclid; full Dirichlet needs L-functions).
- **√2 IS IRRATIONAL** (`isabelle_sqrt2.rs`, 2026-06-13 — the companion capstone):
  `⊢ ¬(∃a. 0<a ∧ ∃b. a·a = 2·(b·b))` — no positive naturals a,b with a²=2b². A 0-hyp
  theorem by INFINITE DESCENT via strong induction; only classical assumption = excluded
  middle. Proof: a solution forces a even (`sq_even_even`, via the odd²-is-odd parity
  argument — no Euclid's lemma needed), a=2c; cancelling 2 (`mult_left_cancel`) gives a
  SMALLER solution b<a (`sq_lt_cancel`), contradicting strong-induction minimality.
  Parity helpers: `parity` (every x is 2c or 2c+1), `odd_not_even`, `mult_left_cancel`,
  `mult_zero_cancel`, `sq_lt_cancel`, `mult_le_mono`. Soundness probe: kernel rejects the
  false positivity-dropped variant (a=b=0 solves it). Built on `isabelle_classical_primes.sml`
  by a 2-phase ultracode pipeline (wf_d7246a73-e08). With Euclid, two of the most famous
  theorems in elementary number theory, both from first principles on the Rust runtime.
  (Maintenance: the ~3229-line classical foundation is now consolidated into the shared
  `isabelle_support/isabelle_nt_helpers.sml` (object logic + Peano + semiring + order +
  divisibility + classical FOL + the genuine prime-divisor theorem). 11 drivers that used to
  embed it verbatim — division, euclid_lemma, euclid_list, euclid, fta, sqrt2, ntbase, flt,
  binom_thm, binom, sum — now carry only their proof delta and the harness splices the
  foundation in front via `common::with_nt_helpers` (commit 10a7a51, −35.5K dup lines). The
  splice is provably behavior-preserving: the removed block was byte-identical to the helper
  in every file and each driver's pre-foundation prefix is comment-only, so prepending only
  reorders comments. `isabelle_classical_primes.rs` now validates the helper standalone. STILL
  embedding a VARIANT foundation (a "PHASE 2"-structured merge artifact, ~80 lines off
  canonical) and NOT yet consolidated: `isabelle_modular` / `isabelle_power` /
  `isabelle_fta_unique` — their proofs need re-verifying against the canonical helper first.
  Nested second-tier dedup (euclid_lemma additions in euclid_list; ntbase additions in the
  Fermat-arc drivers) also remains.)
- **A LIST THEORY by structural induction** (`isabelle_list_theory.rs`, 2026-06-13 — a
  SECOND inductive datatype beyond nat): on the semiring base, build `natlist = Nil | Cons
  nat natlist` with its own list-equality `leq` (refl+subst) + a `list_induct` axiom +
  append/reverse/length by primitive recursion, and prove by structural induction (each
  0-hyp): `append_nil`, `append_assoc`, `rev_append` (`reverse (append a b) = append
  (reverse b) (reverse a)`), **`rev_rev`** (`reverse (reverse l) = l`), `length_append`
  (`length` additive, via add_Suc/add_0). The Isabelle analogue of the HOL4
  `list_laws_verified.sml` — shows the hand-built object logic handles a second inductive
  datatype with its own induction principle. Soundness probe rejects a garbled rev_rev.
  3-seat ultracode fleet (wf_666cb3a1-e29).
- **FUNDAMENTAL THEOREM OF ARITHMETIC (existence)** (`isabelle_fta.rs`, 2026-06-13 — the
  finale that FUSES the list theory with the primes machinery): `⊢ ∀n. 2≤n ⟹ ∃ps. all_prime
  ps ∧ product ps = n` — every n≥2 is a product of primes. A 0-hyp theorem by strong
  induction; only classical assumption = excluded middle. Adds `natlist` + `product` +
  `all_prime` + `product_append` + `all_prime_append` + the `cofactor` lemma (1<d<n ∧ d∣n ⟹
  ∃e. 1<e ∧ e<n ∧ n=d·e) on the classical-primes base, then: `prime_cases` splits n into
  prime (singleton list) or composite (proper divisor d → cofactor e → strong IH on both d,e
  → append their prime-lists, product = d·e = n). Built by a 2-phase ultracode pipeline
  (wf_15cdc379-e01): list/product helpers → FTA (2 seats both proved it). With Euclid +
  √2-irrational, a genuine elementary number theory from first principles on the Rust
  interpreter.
- **FTA-UNIQUENESS arc (in progress)** — the famous hard half (prime factorisation is
  unique), staged: division theorem → gcd + ℕ-Bézout → Euclid's lemma → uniqueness.
  - **Stage 1 — THE DIVISION THEOREM** (`isabelle_division.rs`, 2026-06-13): `⊢ 0<b ⟹ ∃q
    r. a = b·q+r ∧ r<b` (`div_mod_exists`) AND uniqueness (`div_mod_unique`), both 0-hyp.
    Existence by strong induction on a, NO subtraction (a<b→(0,a); else a=b+a2 via the
    le-witness, a2<a, recurse, recompose q:=Suc q2 via mult_Suc_right). 3-seat fleet
    (wf_17792bed-545).
  - **Stage 2 — EUCLID'S LEMMA** (`isabelle_euclid_lemma.rs`, 2026-06-13): `⊢ prime p ⟹
    p∣a·b ⟹ p∣a ∨ p∣b`, 0-hyp, over the structural prime. Proved by the GAUSS DESCENT —
    **no gcd, no Bézout, no integers**: `bounded_euclid` (a<p) by strong induction (divide
    p by a → 0<r<a, `dvd_diff` gives p∣r·b, recurse at r), then general by reducing a mod p.
    Key insight that made it tractable: the gcd/Bézout apparatus (which needs integers over
    ℕ) is entirely avoidable — the descent needs only the division theorem + `dvd_diff`
    (p∣x ∧ p∣(x+y) ⟹ p∣y) + `prime_not_dvd_pos_lt`. 2-phase pipeline (wf_904dd5f8-976).
    Remaining: Stage 3 (done below) → Stage 4 (the uniqueness count argument).
  - **Stage 3 — EUCLID'S LEMMA FOR LISTS** (`isabelle_euclid_list.rs`, 2026-06-13): `⊢
    prime p ⟹ all_prime ps ⟹ p∣∏ps ⟹ in_list p ps` — a prime dividing the product of a
    list of primes IS one of them. Re-derives the list machinery (natlist + product +
    all_prime + a membership predicate `in_list`) on the Euclid-lemma base, proves
    `prime_div_eq` (two primes, p∣q ⟹ p=q, from the structural prime), then the headline by
    list induction on `euclid_lemma`. The key lemma for Stage 4. 2-phase pipeline
    (wf_1b8fb713-66f). [Also: the harness `run_image_env` had a stdin/stdout pipe-buffer
    DEADLOCK on big drivers (>64KB stdin + >64KB output) — fixed commit cad1719 by writing
    stdin on a separate thread; it had hung the Euclid-lemma test.]
  - **Stage 4 (FINALE) — FTA UNIQUENESS** (`isabelle_fta_unique.rs`, 2026-06-13): `⊢
    all_prime ps ⟹ all_prime qs ⟹ ∏ps = ∏qs ⟹ ∀r. count r ps = count r qs` — two prime
    factorisations of the same number are the SAME multiset. Adds `count`/`remove1` via
    CONDITIONAL defining axioms (no native if-then-else over object equality — `ex_middle`
    case-splits pick the branch) + bridging lemmas (`product_remove1`, `count_remove1_self/
    other`, `all_prime_remove1`, `mult_left_cancel`, `product_one_nil`), then `fta_unique`
    by list induction on `prime_in_prime_list`: a prime of ps is in qs, remove one copy,
    cancel it from the product, recurse. 2-phase pipeline (wf_20445576-234). **With FTA
    existence (`isabelle_fta.rs`), the FULL Fundamental Theorem of Arithmetic is now proved
    from first principles on the Rust interpreter — task #75 DONE.** Technique note for
    future work: define a "function with a conditional on object equality" (count, remove1)
    as a const + two conditional axioms (eq-case, neq-case), then `ex_middle` + `disjE` to
    use it; remove1 yields a list-equality (`leq`), so transfer properties via `leq_subst`.
- **MODULAR ARITHMETIC** (`isabelle_modular.rs`, 2026-06-13): congruence mod m is a
  CONGRUENCE RELATION — `cong m a b ≝ (∃k. b=a+m·k) ∨ (∃k. a=b+m·k)` (two-sided, ℕ has no
  subtraction) — proving `cong_refl`/`cong_sym`/`cong_trans` (equivalence) + `cong_add`/
  `cong_mult` (compatible with + and · ⇒ ℤ/mℤ is a commutative ring), each 0-hyp on the
  classical-primes base. Subtlety: `cong_add`'s MIXED cases genuinely need `le_total` — the
  linear order enters even though the statement is purely additive (ℕ can't decide which
  side the m-multiple lands on). The gateway to Fermat's little theorem. 2-phase pipeline
  (wf_0bbaeabe-bc6) + merge.
- **FERMAT'S-LITTLE-THEOREM arc (in progress)** — `a^p ≡ a (mod p)`, staged: powers →
  binomial coeffs (p∣C(p,k)) → binomial theorem mod p (the wall) → FLT.
  - **Stage A — POWERS + MODULAR POWERS** (`isabelle_power.rs`, 2026-06-13): `pow` +
    `pow_one`/`pow_add` (`a^(m+n)=a^m·a^n`)/`pow_mult_base` (`(ab)^n=a^n·b^n`) + `cong_pow`
    (`a≡b ⟹ a^n≡b^n mod m`, induction on n via `cong_mult`/`cong_refl` + a `cong_cong`
    helper). 3-seat fleet (wf_f0e818c6-9ed). Stages B-D remain; B (binomial `p∣C(p,k)`) is
    clean, C (binomial theorem mod p, needs a summation operator) is the known hard wall.
  - **Stage B — BINOMIAL COEFFICIENTS + p∣C(p,k)** (`isabelle_binom.rs`, 2026-06-13, on the
    unified base): `binom` via Pascal + the **absorption identity** `(k+1)·C(n+1,k+1) =
    (n+1)·C(n,k)` (induction on n with k universal via object `Forall`, IH at two points +
    both Pascal directions) + the famous **`p_dvd_binom`** (`prime p ∧ 0<k<p ⟹ p∣C(p,k)`,
    via absorption ⟹ `p∣k·C(p,k)`, `p∤k` + Euclid's lemma). 2-phase pipeline (wf_2f2eeca9-c88).
    Remaining: Stage C (binomial theorem mod p) → Stage D (FLT).
  - **Stage C1 — SUMMATION + TRUNCATED SUBTRACTION** (`isabelle_sum.rs`, 2026-06-13): Pure
    is HIGHER-ORDER, so `sumf : (nat⇒nat)⇒nat⇒nat` is a legit const (pass summands as object
    lambdas, beta_norm after applying f to an index). `sumf f 0 = f 0`, `sumf f (Suc n) =
    sumf f n + f (Suc n)`; `sub` (truncated −) + `sub_self`/`sub_Suc_le`; and the workhorse
    `sum_cong` (`(⋀k. k≤n ⟹ f k = g k) ⟹ sumf f n = sumf g n`, a higher-order induction).
    2-seat fleet (wf_0d8f0cb2-45c).
  - **Stage C2 — THE BINOMIAL THEOREM** (`isabelle_binom_thm.rs`, 2026-06-13 — the hardest
    proof in the tower, the wall): `⊢ (a+b)^n = Σ_{k=0}^n C(n,k)·a^k·b^(n−k)`, 0-hyp. Plus
    the sum-algebra (`sum_mult_l`, `sum_add`, `sum_peel_first` reindex, `binom_n_n` via
    `binom_diag_zero` = `C(n,n+1+j)=0` by single induction with IH at j AND j+1 — no lt
    machinery, `pow_b_sub_Suc`). Induction on n: `(a+b)^(Suc n) = a·S + b·S` [IH +
    right_distrib], distribute into the sum, shift exponents, peel the Suc-n RHS, Pascal-split
    each term into two sums, recombine. 2-phase pipeline (wf_a511fcbc-470), all 3 seats proved
    it.
  - **Stage C1 — SUMMATION + SUBTRACTION** (`isabelle_sum.rs`): `sumf` (higher-order) + `sub`
    + `sum_cong` (see entry above).
  - **Stages C3+D — FRESHMAN'S DREAM + FERMAT'S LITTLE THEOREM** (`isabelle_flt.rs`,
    2026-06-13 — THE SUMMIT): `flt : ⊢ prime p ⟹ a^p ≡ a (mod p)`, 0-hyp (only classical
    assumption = excluded middle; soundness probe keeps the prime premise). Via the
    `freshman_dream` (`prime p ⟹ (a+b)^p ≡ a^p+b^p mod p`): binomial theorem at exp p, peel
    the k=0/k=p endpoints, interior terms divisible by p (`p_dvd_binom` + `sum_all_dvd` +
    `dvd_imp_cong_zero`). FLT by induction on a (`0^p=0`; step `(a+1)^p ≡ a^p+1 ≡ a+1` via the
    freshman's dream + IH + cong_add/cong_trans + `pow_one_base`). Helpers: `sum_all_dvd`,
    `dvd_imp_cong_zero`, `pow_one_base`, `pow_zero_pos`. 2-phase pipeline (wf_263aa14e-2ad),
    all 3 seats proved it. **FERMAT'S LITTLE THEOREM is now proved from first principles on
    the Rust interpreter — completing, with Euclid + √2-irrational + FTA, a tour of the
    landmark theorems of elementary number theory.**
  - **NOTE on the unified base** (`isabelle_ntbase.sml`): the Fermat-arc drivers build on it
    (classical+division+Euclid+modular+powers in one), so they no longer re-derive separate
    foundations — the consolidation paid off for Stages A/B.
KEY GOTCHA across all of it: `Thm.add_axiom_global` returns axioms UNVARIFIED (Free vars,
not schematic) — varify (`Drule.generalize`/`export_without_context` + `zero_var_indexes`)
before `infer_instantiate`/resolution, or instantiation silently no-ops; `forall_elim`
does not beta-reduce (beta-normalise first). The bulk of this was driven by ultracode
proving workflows on the warm checkpoint.

--- historical recon (2026-06-06), kept for context ---

After completing HOL4's prover stack, probed whether our Rust PolyML can run
**Isabelle**. Verdict (since SUPERSEDED): reachable but FAR (months) — yet **no missing
C-RTS primitive blocks a minimal Isabelle/Pure source load**; the hard PolyML coupling
(`PolyML.NameSpace`, structural `PolyML.pretty`, the `CPCompilerResultFun` parse-tree
path at ROOT.ML #226) is vendored SML already compiled into our image. Isabelle/Pure
has a Scala-free ML entry (`poly --eval "val SML_file = PolyML.use" --use ROOT.ML`),
threads/Future are lazy (single-threaded load works), SaveState is save-time-only,
and the version matches (5.9.2).

**First rung DONE** (`isabelle_pure.rs`, `common::isabelle_pure_dir`): the first
Isabelle/Pure ML runs on the interpreter — **23 of 27 Phase-0 files load** on a
basis checkpoint, incl. `ml_name_space` (PolyML.NameSpace round-trips), `ml_system`,
`ml_pretty`, `multithreading`/`synchronized`, `thread_attributes`, `ml_heap`,
`ml_recursive`. Source vendored as a git-ignored sparse blobless clone of
`mirror-isabelle` `src/Pure` (~6 MB) under `vendor/isabelle/`.

**Full recon DONE** (2026-06-06; both gating risks retired). The complete
engineering plan to a minimal Pure load (compile-all-Pure-ML, no theory execution):

- **parseTree introspection — GREEN** (`parsetree_introspect.rs`): the 2nd major
  compiler coupling (Isabelle's `ml_compiler.ML` drives `PolyML.compiler` +
  `CPCompilerResultFun` and walks `PolyML.parseTree`/`PT*`, which HOL4 never does)
  works — compile returns code+tree, the walk renders a `PTtype` to `int`, error
  decls return `code=NONE, tree=SOME`. No longer a risk.
- **The gap inventory collapses to THREE root-cause groups**: (1) int-precision;
  (2) Isabelle `\<...>` symbol notation — **2a** string-literal cartouches (SMALL:
  SML rejects `\<`; cleanest fix = permissive string escape in the lexer / upstream
  `unescapeString`) vs **2b** bare ML antiquotations `\<^here>`/`\<^binding>` (HARD,
  THE structural wall); (3) Isabelle system `Options` env (stub).
- With stubs for the 4 Phase-0 walls + the int/cartouche patches, **Phase 0 = 27/27,
  Phase 1 = 50/50, and 83/90 to "Fundamental structures" — `name.ML`, `term.ML`,
  `context.ML` (the Isabelle KERNEL) load.** No Pure file forks a thread/socket at
  load (single-threaded load is safe).
- **THE real frontier = the ML-antiquotation expander** (`ML_Lex` + `ML_Context`),
  needed by **97 of ~150 remaining Pure files**. This is an Isabelle compile-pipeline
  PORT (months), NOT a polyml-rs runtime gap — and it couples back to the (now-GREEN)
  parseTree path.
- **int-precision — a latent interpreter bug found**: flipping the default to
  arbitrary-precision (`--intIsIntInf`, the real fix that deletes the whole Group-1
  cascade) **deterministically SEGVs our interpreter at `basis/Real.sml` (exit 139)**,
  reproduced via the full Stage1 chain. The runtime bignum itself is fine (IntInf.pow
  works). So near-term = a per-checkpoint shim (retype the Real↔int family to LargeInt
  + supply `Time.seconds`, kept OUT of HOL4); long-term = diagnose the Real.sml SEGV
  then flip. This Real.sml-SEGV-under-arbitrary-int is its own worthwhile runtime bug.

Roadmap (root-cause-grouped, in `[[isabelle-go-signal]]` / task #69): 1 int-shim →
2 string-cartouche pass-through → 3 Options stub → 4 ml_statistics shape → (Phase 0/1
= 50/50, kernel structures load) → 5 diagnose Real.sml SEGV + flip default int →
6 snippet milestone (`val x=1+1` through Isabelle's own `ML_Compiler0`) → 7 kernel
sub-block (term/thm/proofterm — uses only `\<^here>`, textually rewritten by
ml_compiler0) → **8 (LARGE) port the antiquotation expander** → 9 remaining Phase 2/3
volume. Deferred-but-real (frontend-only, NOT load-time): real Future scheduler,
sockets/PIDE/Scala, C FFI, stable `GET_THREAD_ID` (cache one thread object).

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
