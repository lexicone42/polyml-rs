# Correctness & safety

How polyml-rs convinces itself it is a *faithful* and *memory-safe* reimplementation
of Poly/ML's runtime. Two questions matter for a runtime that executes a real
compiler and proof assistants:

1. **Faithfulness** — does it compute the *same answers* as upstream Poly/ML?
2. **Memory safety** — can it be made to corrupt memory or crash?

## Faithfulness: a differential oracle against upstream Poly/ML

The strongest correctness signal is a ground-truth oracle: run the *same* SML
through the real upstream Poly/ML and through polyml-rs, and diff the results. Any
difference is a bug in our port.

- **`tools/build-oracle.sh`** builds upstream Poly/ML out-of-tree (both the
  native-code and the bytecode-interpreter configurations — the latter shares our
  backend, so it is the reference for codegen-level comparisons).
- **`tools/diff-oracle.sh`** runs each SML snippet through both and compares the
  tagged result lines.
- **`tools/diff-corpus/`** holds roughly **1,300 deterministic comparisons** across
  ~30 categories — integer/word/real arithmetic (with seeded random fuzz drivers
  that exercise both the inline opcode path *and* the runtime-call path),
  conversions, text, the structure libraries, and heavy compiler-stress programs
  (Ackermann, deep mutual tail-recursion, bignum factorials, GC-pressure folds).
  Every case is **byte-identical** to upstream.

Beyond the hand-built corpus, polyml-rs runs **Poly/ML's own validation test
suite** (`vendor/polyml/Tests/`, 212 expected-pass + 83 expected-fail programs):
about **265 of 291 pass**, with the rest being genuinely unimplemented basis
features (e.g. some `IEEEReal` rounding-mode corners) rather than wrong answers.

The one apparent arithmetic divergence ever found (`IntInf.andb`/`orb` with a
particular short operand) turned out to be a **latent bug in the upstream stage-0
bootstrap compiler** — polyml-rs reproduces it *byte-for-byte*, which is the
strongest faithfulness statement available: we match upstream even where upstream
is wrong. (Details: `git log` / the bootstrap is recompiled away by the later
self-compilation stages.)

The interpreter and the experimental JIT are also differentially tested against
each other (every installed JIT function, run under both, across varied inputs):
zero real translation divergences.

## Memory safety

polyml-rs is written in safe Rust except where it must manipulate the raw heap
(pointer tagging, object headers, the GC, image loading). Those `unsafe` regions
were audited systematically, and the runtime is fuzzed against untrusted input.

- **`unsafe` audit.** All ~449 `unsafe` blocks were reviewed. Every memory-unsafe
  dereference or write reduces to **one invariant**: the word is a valid in-heap
  pointer of the expected type and size, which the trusted compiler's bytecode
  guarantees over a valid object graph. The SML stack is a fixed allocation with
  bounds-checked access.

- **Garbage-collector soak.** Long GC stress runs under a deliberately tiny heap
  found one real use-after-free (a dangling pointer left below the stack top across
  a collection) and a gap in the GC's self-audit. Both were **fixed and
  regression-fenced** (a test that deterministically crashed before the fix now
  passes; another pins "zero residual from-space pointers" on the heaviest
  workload).

- **Loader fuzzing.** Feeding ~500 mutated images to `poly run` found **two
  structural memory-safety bugs** (a non-closure root and a count/payload
  mismatch), both **fixed**; the denial-of-service hardening held perfectly (zero
  hangs, zero out-of-memory kills, zero panics across the corpus).

### Untrusted images: the `--untrusted` safe mode

The pexport image format carries *untyped* references: a well-formed, in-range word
can point at a wrong-*type* object, and the loader cannot reject that without
whole-image type inference (the *same* exposure upstream Poly/ML's format has). The
trusted SML compiler never emits such a word, so this is not reachable when running
compiler-produced images.

For running *foreign* images, **`poly run --untrusted <image>`** is a memory-safe
mode: every dangerous pointer-follow — the field-load / call / heap read-write
opcodes, the PC-relative constant reads, the RTS argument readers, and the export
object-graph walk — validates the pointer (space-membership + object-header sanity +
per-op shape) before the unsafe use, turning a malicious image's would-be UB (OOB
read/write, wild jump) into a clean `BadImage` halt. The **default (trusted) path is
byte-identical and exactly as fast** — the bootstrap runs the same 1,110,805 steps;
every check sits behind `if self.untrusted`, so the proven-fastest path is untouched.
A committed malicious-image corpus (`tools/malicious-corpus/`,
`crates/polyml-bin/tests/untrusted_corpus.rs`) proves it: each image genuinely SEGVs
in trusted mode and is a clean halt under `--untrusted`; a mechanical lint
(`tools/lint-image-deref.py`) enumerates the whole image-controlled-operand deref
surface and is a regression guard. (The hardening was found, the hard way, to span
three deref *surfaces* — per-opcode operand reads, PC-relative code-stream reads, and
the RTS-argument / export readers — across four adversarial-verification rounds; the
lint exists so a future change re-flags any un-gated deref instead of shipping it.)

*Residuals:* the RTS-argument gate now enforces the full object-length-fits
invariant too (the follow-up noted in earlier revisions of this page — closed).
Two boundaries remain worth stating: running the experimental real-OS-threads mode
together with `--untrusted` is out of the validated envelope; and `--untrusted` is
*memory* safety, **not a sandbox** — the image still runs with the invoking user's
ambient authority (filesystem, environment, stdout). See `SECURITY.md` for the
threat model.

## The parallel memory model (`POLY_PARALLEL=1`)

With the giant lock dropped (P4, `docs/parallel-design.md`), several SML
threads mutate one shared heap at once, so the memory model becomes a
correctness claim in its own right:

- **Hot heap-word accessors are `Relaxed` atomics** (`AtomicUsize` views of
  `repr(transparent)` `PolyWord` cells — LOAD/STORE_ML_WORD, the indirect
  family). A racy SML program therefore observes *unspecified values*, never
  Rust-level undefined behaviour. This was the *measured* choice, not a tax:
  the atomic accessors benchmarked ~9.5% FASTER than plain derefs
  (drift-cancelled A/B; the narrower aliasing semantics free LLVM's codegen).
- **SML `Mutex`/`ConditionVar` protocol words run on hardware atomics**
  (`fetch_add`/`compare_exchange`/`swap` — P3), so SML-level locking is real
  mutual exclusion, fenced by an exact-count hammer (2 threads × 200k
  lock/incr/unlock = exactly 400k, `concurrency_parallel.rs`).
- **Stop-the-world GC**: a collector is *elected* (first requester under the
  scheduler mutex); it waits until every registered peer is provably parked
  (`in_ml == false` AND published roots) before anything moves. Peers park
  only *between* bytecode steps, so an opcode's internal multi-allocation
  sequences are atomic w.r.t. the barrier. `POLYML_GC_AUDIT=1` re-walks every
  root set after each parallel collection in the storm fence.
- **Residual, stated honestly:** *byte*-array accessors remain plain (a racy
  `Word8Array` shared without a mutex is the one surface where the UB-freedom
  argument does not yet apply — wrap it in an SML `Mutex`, as any correct
  program would); and `--untrusted` + threads remains out of the validated
  envelope (above).

The proof obligations are all fenced: byte-identity of the default path
(stage-0 + the 27.7B-step chain), exact-count discriminators under load, the
racy-ref bounds probe, and measured scaling (0.51× two workers, 0.24× a
4-connection compute server — `concurrency_parallel.rs`,
`concurrency_server.rs`).

## Reproducing

The faithfulness and safety harnesses are wired into `tools/regression.sh full`.
See [`REPRODUCING.md`](REPRODUCING.md) for how to build the oracle and run the
demos.
