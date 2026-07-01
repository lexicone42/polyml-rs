# polyml-rs — notes for future participants

A Rust rewrite of Poly/ML's bytecode interpreter, runtime, image loader, and
copying GC. Goal: a faithful port of upstream `vendor/polyml/libpolyml/` with
stronger memory safety. It self-bootstraps the real SML compiler and hosts HOL4
and Isabelle/Pure. See `PLAN.md` for the staged roadmap and `README.md` for the
public capability summary.

This file is the *operational* guide — how to build, run, extend, and the
hard-won gotchas. Detailed history lives in git; correctness/safety methodology
in `docs/correctness-and-safety.md`; the portability design in
`docs/tier-b-portable-images-design.md`.

## Build & run

```
cargo build --release -p polyml-bin

# load + execute the stage-0 bootstrap compiler image (≈1.11M steps → Tagged(0))
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt

# run an SML file one-shot (synthesizes Bootstrap.use + sets -I to its dir)
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt --use script.sml

# self-bootstrap the whole 7-stage chain → writes a polyexport image (~5 min)
cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \
      bootstrap/bootstrap64.txt < bootstrap/Stage1.sml

# the self-bootstrapped image is a real REPL
echo "fun fact 0=1|fact n=n*fact(n-1); fact 10;" | \
      ./target/release/poly run polyexport      # → 3628800

# binary image format (smaller, endian-neutral): convert + run (run auto-detects)
./target/release/poly bic <image> out.bic

# memory-safe mode for FOREIGN/untrusted images (typed-deref validation; default
# trusted path is byte-identical — see docs/correctness-and-safety.md)
./target/release/poly run --untrusted <image>
```

Tests: `tools/regression.sh fast` (always-on, ~2 min) / `full` (+ the HOL4 /
Isabelle / oracle workloads — needs warm checkpoints, see below).

## Bootstrap image structure (important)

`bootstrap/bootstrap64.txt` is **stage 0** — the bare compiler with **no basis
loaded**. It is meant to be driven by piping `bootstrap/Stage1.sml` to stdin with
`-I <srcdir>` so it can find basis sources (`polyimport bootstrap64.txt -I . <
Stage1.sml`). Consequences:
- `1 + 1;` is a **type error** — `+` is an unregistered overload at the bare REPL.
- Infix decls and overloads are not in scope until `basis/InitialBasis.ML` runs.
  For minimal arithmetic, prepend: `infix 6 +;  RunCall.addOverload FixedInt.+ "+";`
- `poly run --use file.sml` synthesizes `Bootstrap.use "file.sml"` to stdin, sets
  `CommandLine.arguments` to `["-I", <dir>]`, and redirects real stdin from
  /dev/null so the REPL exits on EOF. (`-- ARGS` after the image populates
  `CommandLine.arguments()` for any SML that scans args.)

## Architecture & gotchas

- Upstream reference: `vendor/polyml/libpolyml/bytecode.cpp` is the dispatcher we
  port. Every non-trivial opcode handler in
  `crates/polyml-runtime/src/interpreter/mod.rs` cites its upstream line range —
  keep that.
- **Don't merge the RESET variants.** `INSTR_RESET_N` (drop top N) and
  `INSTR_RESET_R_N` (preserve top, drop N below) look identical but aren't;
  merging them silently corrupts every loop using RESET to discard a result. See
  the comment near `INSTR_RESET_1` in `mod.rs`.
- **RTS calling conventions** (the usual arity-bug source):

  | SML wrapper | C signature | Our arity |
  | --- | --- | --- |
  | `rtsCallFastN` | N args, no threadId | Arity-N |
  | `rtsCallFullN` | (threadId, N args) | Arity-(N+1) |
  | `rtsCallFast0 "X"` on `unit -> ?` | C is `(void)` but SML passes unit | Arity1 |

  (Last row: PolyML's C side silently accepts the extra arg — x86-64 ignores
  unused register args — so our typed dispatch must match the call site exactly.)
  RTS dispatch tokens are baked into warm checkpoints by `register()` **order** —
  reordering `rts.rs` silently mis-dispatches stale checkpoints (e.g. copySign→pow).
  Rebuild all checkpoints after any table order/count change.
- **Heap:** default 1.6 GB (200M words × 8). `with_default_alloc_space` takes a
  *word* count (footgun). `POLYML_HEAP_BYTES` env overrides the default in every
  heap-attaching subcommand (set 6–8 GB for heavy proving drivers; a *larger*
  heap can postpone GC past the working set and OOM around stage 6). Malformed
  values warn on stderr and fall back to the default; values under the 1 MB
  sanity floor warn but are honored. Heap exhaustion halts CLEANLY (`InterpError::HeapExhausted`,
  naming `POLYML_HEAP_BYTES`) — never a Rust panic, and never GC-retry-on-full
  (alloc-pointer-caching hazard; see `MemorySpace::try_alloc`). The Cheney GC
  fires at 80% (override `POLYML_GC_THRESHOLD`; `POLYML_GC_QUIET=1` silences the
  per-cycle log; `POLYML_GC_AUDIT=1` checks for residual from-space pointers —
  slow, debug only). Boolean env vars (`POLY_REAL_THREADS`, `POLYML_GC_QUIET`,
  `POLYML_GC_AUDIT`, the `JIT_*`/`WHOLE_REGION_*` debug flags) parse their
  *value* via `polyml_runtime::env_flag`: unset/empty/`0`/`false`/`off` = OFF,
  anything else = ON — so `=1` enables as documented and `=0` really disables
  (they used to be presence-only).
- **Interrupts:** SIGINT raises the SML `Interrupt` exception (`crate::interrupt`
  + a coarse `run_until` poll).
- **Real threads (`POLY_REAL_THREADS=1`, default OFF):** genuine `Thread.fork` /
  `Thread.Mutex` / `ConditionVar` over OS threads sharing one heap, under a
  **giant lock + safepoint stop-the-world GC** (`crates/polyml-runtime/src/sched.rs`,
  port of upstream `processes.cpp`). This is **concurrency, not parallelism** —
  exactly one mutator runs bytecode at a time (upstream's interpreter-mode model).
  The 2-thread mutex demo runs end-to-end on the `polyexport` REPL
  (`crates/polyml-bin/tests/concurrency_mutex_demo.rs`, `…/concurrency_support/mutex_demo.sml`
  → counter = 200000); the runtime-level GC-handshake + fork-TOCTOU + H1/H2
  soundness controls are `polyml-runtime/tests/concurrency_gc_handshake.rs`.
  Default OFF keeps the bootstrap/REPL/HOL4/Isabelle paths **byte-identical**
  single-threaded (`fork` is a dormant no-op stub). Keystone: the basis forks a
  SIGNAL thread at startup that loops on `PolyWaitForSignal`; once `fork` really
  spawns it, that thread MUST **park** (it is flagged a daemon + blocks in
  `try_thread_rts`), else it busy-spins the giant lock and hangs the REPL. Still
  missing for *full* concurrency: a thread scheduler/preemption beyond the
  cooperative safepoint yield, and `Thread.Thread` attribute fidelity. Design:
  `docs/concurrency-and-jit-roadmap.md`.

## Diagnostic tooling (use it before hand-tracing)

Build a histogram before guessing — it found the killer RESET bug in 30 min after
weeks of failure. `Interpreter::enable_diagnostics()` then
`take_diagnostics().hot_pcs(N)` for the hottest PCs. CLI: `poly run --profile`
(hot-code histogram on exit), `--trace-rts` (log every RTS call), `--jit
--profile` (per-function JIT cache-hit + likely blocker opcode),
`POLY_CHECKPOINT_EVERY=N` (step counts). The `disasm` module + `poly disasm`
decode a function's bytecode for codegen forensics.

## Faithfulness (the differential oracle — use it)

Ground truth: run the same SML through real upstream Poly/ML and through `poly
run`, diff results. `tools/build-oracle.sh [interp]` builds upstream at
`/tmp/polybuild[-interp]/poly` (the `interp` build shares our bytecode backend —
the reference for codegen debugging). `tools/diff-oracle.sh --dir tools/diff-corpus`
runs ~1,300 comparisons (Basis + compiler-stress + seeded LCG fuzz drivers that
exercise BOTH the inline opcode path and the ref-forced RTS path), all
byte-identical. **Lesson:** test every dispatch path — the PolySubtractArbitrary
negation bug lived in the RTS path the opcode-path fuzzing missed. The lone
`IntInf.andb/orb` divergence is a **latent upstream stage-0 bug** we reproduce
byte-for-byte (not ours). Full methodology + the memory-safety audits:
`docs/correctness-and-safety.md`.

## Performance & JIT

Interpreter: ~92M steps/sec single-core (basis load 1.8B steps ~19s; the 7-stage
chain 27.7B steps ~5 min). **Honest vs-upstream numbers (`tools/bench.sh`, 12
classic-SML benchmarks): geomean ~4× slower than upstream's OWN bytecode
interpreter, ~32× vs native codegen — but only 1.4–2.3× on GC/alloc-bound work
(the GC is competitive; the dispatch loop is the headroom). All 12 byte-identical
to upstream. Full table: `docs/benchmarks.md`.** Most of the ~8× gain: caching the GC threshold in an
`AtomicUsize` (was an env read per step), pre-computing `gc_trigger_words`, and an
in-crate `run_until` loop that picks the fast (non-instrumented)
`step_impl::<false>` monomorphisation once. `poly run --profile` dumps hot
opcodes; next-hottest are INDIRECT_LOCAL_B0/B1 + the JUMP family (diminishing
returns).

JIT (`poly run --jit`): translates trusted bytecode to Cranelift IR; runs the full
pipeline correctly (bootstrap, 7-stage chain, all HOL4 tests). ~76% of code
objects translate, ~823 install. After Phase-0 install/trampoline work it is
**~2% faster** than the interpreter — a modest win; its honest value today is a
**correctness testbed** (the interp-vs-JIT differential: `poly diff`). The wall is
hot-function COVERAGE: the top-called functions are blocked by CALL_CONST_ADDR /
CALL_LOCAL_B, which model a non-popping call convention (args persist across the
call, RETURN_N collapses them) that the per-call trampoline can't express — no
install-gate can unlock them. Debug env: `JIT_DUMP_IR`, `JIT_TRACE_CALLS`,
`JIT_ONLY_IDX=N`, `JIT_INSTALL_LIMIT/SKIP`, `JIT_TRACE_RETURNS`, `JIT_TRAMP_*`. The
bisection harness lives in `install_all_jit_entries` (polyml-jit/src/lib.rs).

**Whole-region JIT (`poly run --whole-region`, default OFF): BUILT + measured — sound
but NOT a speedup.** The hypothesis was that whole-region compilation (a shared-stack
non-popping convention that *can* express the calls the per-function JIT bails on)
was "the only road to real native speed". It was built end-to-end (memory-backed
translator → region fixpoint → live do_call boundary → GC-safepoints → GC-safe alloc
→ dynamic-call trampoline with raise fidelity; `crates/polyml-jit/src/{memtrans,
boundary,region}.rs`) and **measured on the canonical heavy workload (the full 7-stage
self-bootstrap, 27.7B steps): BYTE-IDENTICAL flag-on vs flag-off (9.8M native
dispatches — an exhaustive soundness proof) but 0.87× wall-clock — a ~15% SLOWDOWN.**
Only ~2.8% of real-workload steps go native: the compiler's genuine hot path (parser/
typechecker/optimizer) uses closures/exceptions outside the compilable subset and
BAILS; only small leaf regions compile, and a per-call dispatch tax does the rest.
The per-region microbench best-cases (21.8× pure-loop, 3.45× call-bound) were real but
unrepresentative. **Verdict: the tight threaded interpreter wins on real workloads;
whole-region's honest value is the same as `--jit`'s — a correctness testbed**, now
validated at self-bootstrap scale. Flag-gated, default-off, default byte-identical;
stopped at the S5 kill-switch (no productionize). Full write-up: the
`jit/whole-region:` commit series (git log).

## Portability

Image portability is validated on **five 64-bit architectures across both
endiannesses** — x86-64 Linux, arm64 macOS (real hardware), riscv64, s390x
(big-endian), ppc64 (big-endian) — all running the same x86-64-built image
byte-identically (1,110,805 steps → Tagged(0)). Design +
recipe: `docs/tier-b-portable-images-design.md`; macOS runbook:
`docs/apple-silicon-cross-arch-demo.md`.

Hard-won facts:
- Run a cross-arch target with **`cross`** (containerized gcc toolchain + bundled
  qemu): `CROSS_CONTAINER_ENGINE=podman cross run --target <T> -- run <image>`.
  For s390x/ppc64 use the newer `:main` image
  (`CROSS_TARGET_<T>_IMAGE=ghcr.io/cross-rs/<t>:main`) — the default images ship
  glibc < 2.25 and fail Cranelift's build script. A static-PIE binary from a
  hand-rolled lld link SEGVs under qemu-user; cross's in-container qemu is the
  reliable path.
- **Endian-cleanliness:** bytecode immediates are little-endian *by format*, so
  decode with `from_le_bytes` on any host. Native heap data (PolyWords, string
  chars) must use `_ne_bytes` — `_le_` there byte-flips on big-endian (the two
  bugs that made s390x SEGV; both fixes `_le_ → _ne_`, byte-identical on LE).
- **Cross-*word*-size (64↔32) carries DATA, not code.** The object graph
  reconstructs on a 32-bit host (the loader boxes oversized tagged ints), but
  64-bit-compiled bytecode bakes in 64-bit word-size constants (the 2⁵⁶−1 header
  mask, the −2⁶² tag bound), so it can't execute faithfully — upstream's
  documented limitation. The codebase compiles for `i686` (4 host-width fixes).

## HOL4 harness

The full HOL4 prover stack runs on the interpreter — kernel → parser → bool →
tactics → rewrite → simp → arithmetic → **Datatype** → mesonLib/metisLib/tautLib.
Capstones: verified sorts (insertion/merge/quick), Euclid GCD, a verified stack
compiler, a verified BST, list laws; the Pelletier FOL suite (46/47 by MESON,
matching upstream). Tests: `crates/polyml-bin/tests/hol4_*.rs` (`#[ignore]`, need
warm checkpoints).

- Build warm checkpoints: `tools/build-hol4-checkpoints.sh [target]` →
  `/tmp/hol4_<target>` (the ladder: kernel → theory → parse → bool → tactic →
  … → datatype). Drive a driver: `tools/sml-exp.sh <checkpoint> <driver.sml>`
  (prints one structured summary; survives a flaky terminal).
- Keystone gotchas:
  - **A pervasive `Interrupt` must be bound** before `Portable.sml`
    (`exception Interrupt = RunCall.Interrupt;`). Unbound, `handle Interrupt | _`
    parses as catch-all-reraise, silently breaking `Lib.total`/`can` and ~22 parse
    modules.
  - **The HOL4 quote-filter runs on our interpreter** (`HOLSource.inputFile`) — it
    rewrites ``…`` term quotations + in-body unicode to `[QUOTE …]` / `\DDD`
    escapes, so quotation-carrying `.sml` loads with no external toolchain.
  - **Neutralize `export_theory`/`new_theory`'s implicit export** (set
    `Globals.interactive := true`) — the on-disk PP-to-file path trips the
    interpreter's exception-unwinding halt; we drive HOL4 as a REPL, never write
    `.dat`.
  - **Pipe source per-declaration** to the REPL: an uncaught exception through one
    `PolyML.use` trips the "exception packet called as a closure" halt.
  - SAT/`minisat` is **not** a blocker — `HolSatLib` falls through to HOL4's
    pure-SML DPLL when the binary is absent.

## Isabelle harness (the number-theory tower)

Isabelle/Pure loads (261/285 files — the rest need the Scala frontend) and proves
real mathematics by genuine LCF kernel inference. The tower spans object logic →
Peano/semiring → order/divisibility → strong induction → classical FOL, and
proves the landmark theorems of elementary number theory: **Euclid's infinitude of
primes, √2 irrational, the Fundamental Theorem of Arithmetic (both halves),
Fermat's little theorem, Euler's theorem + criterion, Wilson's theorem (+ converse
+ the full iff), the Chinese Remainder Theorem, Fermat's two-square theorem,
Euclid's even-perfect-number theorem, primes ≡ 1 and ≡ 3 mod 4, Zeckendorf,
Pythagorean-triple parametrization, Fibonacci/Cassini, the binomial theorem +
Vandermonde**, **Lagrange's four-square theorem** (`∀n. ∃a b c d. n =
a²+b²+c²+d²` — closed via the Euler descent; see `docs/four-square-progress-*.md`),
— Gauss's golden theorem — the **QUADRATIC RECIPROCITY LAW** (`(p/q)(q/p) =
(−1)^(((p−1)/2)((q−1)/2))`, via Gauss's lemma → the Eisenstein bridge → the
lattice-point count; `tests/isabelle_support/qr_resume/`, 5 committed pieces), and
**BERTRAND'S POSTULATE** (`∀n. 0<n ⟹ ∃ prime p. n<p≤2n`, the full Erdős proof:
central-binomial bounds → the 4^(2n/3) refinement → the threshold contradiction
(W1) closed by a fixed-exponent `b=⌊(s+9)/4⌋` poly-vs-exp induction → a fat-margin
s=35 case + the small-n chain to 631; `tests/isabelle_support/bertrand_resume/`,
7 committed pieces, ~224B steps / 12 GB heap). Each
is a test in `crates/polyml-bin/tests/isabelle_*.rs` plus a `.sml` driver, fenced by
`regression.sh full`. The number-theory tower has no open partials.

How it works:
- Warm checkpoint `/tmp/isabelle_pure` (`tools/build-isabelle-pure.sh`): reloads
  in ~2s. A driver's **first line must be `val () = restore_pure_context ();`**
  (the generic context is thread-local, lost on reload). The REPL namespace is
  Isabelle ML (`writeln`, not `print`).
- Drivers build on a shared foundation spliced in by the test harness
  (`common::with_nt_helpers` → `with_ntbase` → `with_gcd` → `with_wilson` → …) so
  each driver carries only its proof delta. Reuse the highest applicable splice
  tier rather than re-embedding the foundation.
- **THE load-bearing gotcha:** `Thm.add_axiom_global` returns axioms
  **UNVARIFIED** (Free vars, not schematic). You must **varify**
  (`Drule.generalize` / `export_without_context` + `zero_var_indexes`) before
  `infer_instantiate` / resolution, or instantiation **silently no-ops**.
  `forall_elim` does **not** beta-reduce — beta-normalise first.
- Adding a new constant **extends the theory**: route *every* downstream cterm
  through the **one** final context (built on the extended theory) and re-`varify`
  reused base lemmas onto it — else cross-theory cterm mismatches / silent no-op.
- Use **`prime2`** (the structural prime `1<p ∧ ∀d. d∣p ⟹ d=1∨d=p`). The legacy
  `prime`/`primePredAbs` has a de-Bruijn capture bug (its raw `Bound 0` is captured
  by `dvd`'s inner existential) and is **dead** — don't revive it.
- Soundness discipline: assert proved theorems are 0-hyp (`Thm.hyps_of = []`),
  audit axioms (`Theory.all_axioms_of` — the only classical assumption should be
  `ex_middle`), and add probes that confirm the kernel *rejects* false variants.
- SML's comment lexer **nests**: a stray `(*` inside a comment (e.g. an ASCII
  "(·") reads as an unterminated nested comment. Avoid stray `(*`/`*)` in comments.

## Open issues

- ~~Untrusted-image type-confusion~~ **CLOSED (#96)**: `poly run --untrusted` is
  the typed-deref safe mode (space-membership + header sanity + per-op shape,
  across all three deref surfaces: opcode operands, PC-relative code-stream
  reads, RTS-arg/export readers). The trusted default is byte-identical. Fenced
  by `tools/malicious-corpus/` + `untrusted_corpus.rs`;
  `tools/lint-image-deref.py` is the surface-completeness guard. NB it is
  *memory* safety, not a sandbox (see `SECURITY.md`).
- **RTS breadth**: much is now REAL (each ported from the cited upstream C,
  differential-verified byte-for-byte): `OS.Process.system` (fork/exec sh -c,
  #141), `Date` local-time (localtime/strftime, #141), IO-error SysErr (#136),
  and **TCP/UDP sockets** over libc (Wave 1b — `mod socket_rts` in rts.rs; an
  SML echo server round-trips through the kernel, `tests/sockets.rs`).
  **Sockets are BLOCKING, not upstream's FIONBIO+ThreadPause** (the scheduler
  is off by default; the one mutator just blocks — see the divergence note on
  `mod socket_rts`). Still stubbed → raise catchable SysErr (never fake
  success; #135, fenced by `tests/rts_defang.rs`): C FFI, Signal.signal
  delivery, SaveState, Posix, socket IPv6/DNS. Load-bearing carve-outs that
  must NOT raise (measured against the chain): `getConst` (OSSpecificGeneral
  code 4) errno tables + `PolyPosixCreatePersistentFD` (Posix
  stdin/stdout/stderr) at basis load, `PolySetSignalHandler` at REPL startup,
  IO codes 17/18/20/22/27 (REPL stdin). **register() ORDER is frozen** — a
  fingerprint unit test pins 228 entries; newly-activated stubs must have
  their arity RE-DERIVED from the SML `rtsCallFullN` site (the old stub
  arities were systematically wrong — latent, since unreachable).
- Real OS threads exist behind `POLY_REAL_THREADS=1` (giant lock + safepoint GC,
  see Architecture); a **preemptive scheduler** (beyond cooperative safepoint
  yielding) and full `Thread` attribute fidelity are still open (task #140,
  stage 2 = breaking the giant lock for true parallelism). Whole-region JIT
  was BUILT + measured (sound but a net slowdown — see Performance & JIT); a real
  native *speedup* is now believed out of reach for this interpreter (the tight
  threaded loop wins). Windows remains unimplemented.

(The Isabelle number-theory tower is complete — Lagrange's four-square theorem,
the last open partial, is proved; see `docs/four-square-progress-*.md`. It is
fenced + reproducible: `tools/build-l4-checkpoint.sh` builds the base checkpoint,
then `cargo test -p polyml-bin --test isabelle_four_square four_square_full_theorem
-- --ignored` re-proves it; proof artifacts + a README live in
`crates/polyml-bin/tests/isabelle_support/four_square_resume/`.)

## Persistent checkpoints

`/tmp/*` checkpoints are symlinks into `/var/tmp/polyml-rs` (survives reboots).
After an outage run `tools/persist-ckpts.sh` to relink — no rebuilds.
