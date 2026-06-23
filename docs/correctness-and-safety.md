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

### The one honest caveat

The pexport image format carries *untyped* references: a well-formed, in-range word
can point at a wrong-*type* object, and the loader cannot reject that without
whole-image type inference. The trusted SML compiler never emits such a word, so
this is not reachable when running compiler-produced images — but it means
**loading a deliberately-malicious image is not guaranteed safe.** This is the
*same* exposure upstream Poly/ML's format has. Hardening the interpreter's
dereferences with a typed-pointer check is tracked future work.

## Reproducing

The faithfulness and safety harnesses are wired into `tools/regression.sh full`.
See [`REPRODUCING.md`](REPRODUCING.md) for how to build the oracle and run the
demos.
