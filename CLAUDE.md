# polyml-rs — notes for future participants

## What this is

A Rust rewrite of PolyML's bytecode interpreter, runtime, and image
loader. Goal: faithful port of upstream's `vendor/polyml/libpolyml/`
semantics with stronger memory safety and a friendlier development
loop. See `PLAN.md` for the staged roadmap.

## Demo (Monday)

Four things to show:

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
a real pexport text file. **The bootstrap loop is closed
end-to-end:**

```
$ cat > /tmp/quick.sml <<'EOF'
val () = Bootstrap.use "basis/build.sml";
val () = PolyML.export("/tmp/my_export", fn () => ());
EOF
$ cd vendor/polyml
$ ../../target/release/poly run bootstrap/bootstrap64.txt < /tmp/quick.sml
# ... loads all 94 basis files, writes the pexport snapshot ...
Result: Tagged(0)
$ ../../target/release/poly load /tmp/my_export
Loaded /tmp/my_export
  root closure -> code object, len=11 bytes=88, is_code=true
$ ../../target/release/poly run /tmp/my_export
Executing (cap 5000000 steps)…   # starts executing the re-loaded image
```

`PolyML.shareCommonData` is still a no-op (deduplication-style
optimization; safe to skip).

Heap default is 2 GB; the Cheney-style copying GC in
`crates/polyml-runtime/src/gc.rs` keeps the working set bounded
to ~100 MB through the whole chain. Auto-triggered at 80% fullness
(override with `POLYML_GC_THRESHOLD`); per-cycle log can be silenced
with `POLYML_GC_QUIET=1`, full correctness audit with
`POLYML_GC_AUDIT=1` (slow — checks for residual from-space pointers
across all interpreter state after each collect).

### 4. HOL4 theorem-proving runs through our runtime

```
$ cargo test --release -p polyml-bin --test hol4_recon \
    recon_via_checkpoint_proves_implication_self -- --nocapture
... 90 seconds ...
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

## JIT status (60.12% translation, executes hand-crafted only)

The JIT translates bytecode to Cranelift IR. 60.12% of real bootstrap
code objects compile cleanly. Coverage report via:

    cargo test --release -p polyml-jit --test coverage_bootstrap -- --nocapture

**Caveat: translation coverage != execution coverage.** Hand-crafted
unit tests (~137 passing) cover individual opcodes correctly, but
real SML compiler output combines them in ways the unit tests don't,
and JIT'd-and-installed real bytecode tends to segfault during
bootstrap. Bisection harness:

    JIT_BOOTSTRAP_INSTALL=N cargo test --release -p polyml-jit --test jit_bootstrap_run

install=23 works; install=24 crashes. Each diagnosed function reveals
a different semantic gap (stack effect, capture layout, edge-case
arithmetic, etc.). The 24x speedup on a small arithmetic function
(`jit_speedup_bench.rs`) is real — but only for code that matches
the unit tests' shape.

End-to-end validation test:
`crates/polyml-jit/tests/jit_call_const_addr8_end_to_end.rs` —
caller bytecode pushes 7, calls a JIT-cached closure via real
`CALL_CONST_ADDR8`, gets 107 back. This works.

Plumbing in place: `Interpreter::install_jit`, `do_call` JIT-cache
check, `closure_call_trampoline` thread-local routing, JIT-to-JIT
chaining via `jit_dispatch_closure_call`. All correct in isolation.

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
