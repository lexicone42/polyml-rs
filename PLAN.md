# polyml-rs — Stage 2+ Plan

> Output of Stage 1 (research). Pessimistic estimates. Read alongside
> `notes/boundaries.md`, `notes/hard-problems.md`, `notes/bootstrap.md`,
> `notes/runtime-*.md`, `notes/codegen-native.md`, `notes/heap-image.md`.

---

## 0. Anchor: what we're building

**polyml-rs** = a Rust rewrite of PolyML's runtime + a Cranelift-based
codegen replacement, with the long-term goal of architecture-portable
heap images across x86_64 / aarch64 / riscv64 (and 32/64-bit
variants).

**Ambition: production replacement for upstream PolyML**, not a research
demo. We will not declare victory at "it runs hello-world"; the bar is
that real workloads (Isabelle, HOL) run on it within the agreed
performance target. That implies multi-year scope and we shouldn't
pretend otherwise.

We are **not** rewriting the SML compiler frontend. PolyML's compiler is
in SML and we use it as-is via the existing codegen seam (`GENCODE.sig`,
one function: `gencodeLambda`).

Three concentric goals, smallest first:

1. Run an *existing* PolyML heap image on the new Rust runtime,
   initially via a ported bytecode interpreter (no Cranelift yet).
   The runtime must be able to load `bootstrap64.txt` end-to-end —
   no dependence on upstream `poly` at build time.
2. Replace the interpreter's hot path with Cranelift-emitted native
   code, still loading the same heap images.
3. Produce architecture-portable heap images via a new `bicimage`
   format so cross-arch deployment doesn't require rebuilding from
   source.

---

## 1. Monday milestone (the thinnest end-to-end slice)

**Demo goal**: run `print "hello\n"` from a heap image built by
upstream PolyML, executed by the new Rust runtime, with the program
output appearing on stdout.

### What's real

- Minimal Rust `libpolyml`:
  - `TaskData` with the critical fields (`allocPointer`, `allocLimit`,
    `stackPtr`, `stackLimit`, handler chain head, exception slot)
  - `MemMgr` with permanent + local + code spaces, just enough to load
    one heap image
  - Heap-image loader: read the existing pexport text format, populate
    permanent spaces, restore object pointers, set boot arch
  - Allocation trampoline (`heap_overflow_trap`) routing into a stub
    `quick_gc` (which doesn't actually collect — just dies on overflow)
  - Stack-overflow trampoline (also a stub: dies)
  - RTS table sufficient for `print` — really just `polyBasicIOWriteString` and a couple of helpers
  - Process startup + entry to the root function

- The heap image: produced by **upstream** `poly` compiling a one-line
  SML file (`val () = print "hello\n"`) and saved via the existing
  pexport format.

### What's stubbed

- GC: any real collection. We allocate from a fixed-size arena and
  crash on overflow. Heap images small enough to fit.
- Cranelift codegen: not yet wired in. The heap image contains *native
  code from upstream*, which we run directly. (Caveat: this means
  Monday demo runs only on the same arch as upstream — we cheat on
  portability for the demo.)
- Threading: single-threaded. No `gctaskfarm`, no `BroadcastInterrupt`,
  no `InterruptCode`. The stack-limit poisoning mechanism isn't needed
  for one thread.
- Bytecode interpreter: not ported. Can't load `bootstrap64.txt` yet —
  but we don't need to for the demo.
- FFI: not real. The one RTS call (`writeString`) is hardcoded.
- Save state, modules, debugger, profiler: all absent.
- Exception handling: not exercised by the demo (no `raise`).

### Why this slice

- **Validates the runtime↔compiled-code interface.** If `print "hello"`
  works, the alloc trap mechanism, stack scanning convention, and code
  object layout are all confirmed to interoperate end-to-end.
- **Forces us to read every byte of the existing pexport format**
  during loader implementation. This is groundwork for the eventual
  portable format.
- **Cheap rollback**: it's mostly C-shape Rust code. We're not yet
  committed to Cranelift integration choices that turn out wrong.

### Estimated effort (pessimistic)

- 2 weeks engineer time for the loader (parsing pexport, restoring
  references, address tables)
- 1 week for the minimal TaskData / memmgr / alloc trampoline
- 1 week for FFI shimming the one `print` call
- 1 week glue / debugging / "why is this exec page not mapped" hell
- **5 weeks total** to first hello-world demo

Realistically: assume 7 because the *first* time through anything new
takes 50% longer than estimated.

---

## 2. Stage 2 phases beyond Monday

> **Reordered**: interpreter port comes *before* Cranelift, because we want
> off the "upstream `poly` as build-time dep" crutch as early as possible.
> Once the interpreter works, every later phase has a real Rust-only
> baseline to compare against and to fall back to.

### Phase 2.1 — Bytecode interpreter port (~6 weeks)

Port `libpolyml/interpreter.cpp` and `bytecode.cpp` to Rust. End-state:
the Rust runtime loads `bootstrap64.txt`, runs the whole SML compiler
interpreted, and can compile small SML programs into pexport images
itself. **At this point we no longer need upstream `poly` for
anything.**

1. **Read interpreter.cpp + bytecode.cpp + int_opcodes.h end-to-end** (1w)
   before coding. The opcode list is the contract.
2. **Implement opcodes** (3w). Probably 80+ ops; many are trivial
   load/store/branch. Keep parity with C++ exactly; no clever
   rewrites until we have a working baseline.
3. **TaskData / SaveVec / RTS-call plumbing for interpreter** (1w).
   The interpreter uses the same allocation trap mechanism as native
   code, so this overlaps with the Monday-milestone code.
4. **Debugging and Stage1-7.sml validation** (1w). Run the full
   bootstrap pipeline on our runtime. If Stage7 produces a heap
   image, we win.

**Risks**:
- The interpreter shares conventions with native code (TaskData
  layout, code-object layout, exception chain). Mismatches between
  what we plumb here and what later Cranelift code does = subtle bugs.
  Read both `arm64.cpp` and `interpreter.cpp` for the shared
  invariants *before* committing to the structs.
- Opcode list might be wider than we think. Interpreter perf isn't
  the goal — *fidelity* is. Don't optimize until correctness is
  there.

### Phase 2.2 — Cranelift backend, x86_64 (~8 weeks)

Replace the interpreter's hot path with Cranelift-emitted native
code. The interpreter remains as a fallback (and as the bootstrap
loader). **Target only x86_64 native (no 32-in-64) for this phase.**

0. **Stack-map spike** (1w). Before any real lowering — write a
   hand-crafted CLIF function with safepoints exactly where we'd
   want them (function entry, every alloc), dump the stack-map
   table, verify the runtime can consume it. If this doesn't fit,
   it's better to discover that now than 6 weeks in.
1. **BIC → CLIF lowering** (3w). Implement `bic_to_clif` for the ~20
   `BIC*` constructors. Notable subcases:
   - `BICArbitrary`: two-arm lower (fast path + RTS call)
   - `BICCase`: lower to Cranelift `br_table`
   - `BICRaise`/`BICHandle`: on-stack chain, no `try_call`
   - `BICLoop`/`BICEval` tail: `tail` calling convention
2. **Stack-map integration** (1w). Mark `GeneralType` SSA values as
   GC refs; cranelift-frontend inserts spills. Hook into a
   runtime-side table keyed by PC.
3. **Code-object emission** (1w). Wrap each Cranelift module into the
   PolyML code-object layout with constant pool + trailing offset.
4. **RTS-call codegen** (1w). Per-target trampoline; CC bridging
   between `tail` and C.
5. **Compile the compiler with Cranelift** (1w plus uncertainty).
   Run Stage7.sml through our Cranelift backend, producing a fully
   native compiler heap image. This is the real correctness test.

### Phase 2.3 — Real GC (~6 weeks)

Replace the stub allocator with a real GC. Order matters: until this
phase, we've been getting away with a fixed arena that eventually
runs out.

1. **QuickGC** (minor) (2w). Copying collector over the allocation
   area. Single-threaded.
2. **Mark/Copy/Update major GC** (3w). Single-threaded. Forward
   pointers in length words. Don't yet bother with parallel
   `gctaskfarm`.
3. **Weak refs + tombstones** (1w). Enough for basis-library weak-ref
   paths.

**Defer**: parallel GC, sharing phase, profiling. Single-threaded GC
is correct, just slow.

### Phase 2.4 — Concurrency & interrupts (~3 weeks)

Now that GC works single-threaded, add threading.

1. **OS-thread-per-ML-thread**, `schedLock` global. (1w)
2. **Stop-the-world by poisoning `stackLimit`** from another thread.
   Lock-protected stack-limit access. (1w)
3. **`InterruptCode`** + the request queue (`kRequestInterrupt`). (1w)

**Defer**: parallel GC, lock-free anything. Single global scheduler
lock is fine for early bring-up.

### Phase 2.5 — Second arch (aarch64) (~4 weeks)

Re-target Cranelift to aarch64. Most of the work is in the
runtime↔compiled-code interface details:
- Register convention (X26/X27/X28 today; do we keep that?)
- Signal handling / `InterruptCode`
- Code-cache flushing (Arm requires explicit `mcr` on Linux)

The Cranelift side is mostly free — `tail` CC and stack maps work on
aarch64 already.

### Phase 2.6 — macOS support (~4 weeks)

Linux-only until now. macOS adds: Mach-O exporter (we have a
reference in `vendor/polyml/libpolyml/machoexport.cpp`), different
signal handling (mach exceptions vs POSIX signals — choose one),
W^X JIT memory (`pthread_jit_write_protect_np` on Apple Silicon),
codesigning quirks. aarch64+macOS is the harder corner; x86_64+macOS
is usually easier.

**Risk**: Apple's restrictions on JIT memory have tightened over
recent macOS versions. May need entitlements or hardened-runtime
exceptions for the final binary. Verify on actual hardware early in
the phase.

### Phase 2.7 — Portable image format (`bicimage`) (~6 weeks)

Implement option E from `notes/hard-problems.md` §5: portable data +
embedded BIC for code objects.

1. **Spec** (1w). Header (magic, version, word-size,
   endianness, tagging rules), object table format, BIC encoding for
   code objects, dependency/identity hashes.
2. **Writer** (2w). New exporter mode that emits `bicimage` instead of
   pexport. Reuses the existing CopyScan but encodes objects differently.
3. **Reader / loader** (2w). Parse format; for each code object, invoke
   Cranelift to emit native code for the current arch.
4. **Cache** (1w). After a portable image is loaded once, write a
   `image.<arch>.cache` next to it; on subsequent loads, skip codegen
   if the cache is fresh.

**Risk**: BIC is internal to PolyML and may drift. We pin a BIC
version number into the image header and refuse incompatible loads.
First time we change BIC upstream, we'll feel this pain.

### Phase 2.8 — Hardening (~ongoing)

Tests, fuzzing, integration with Isabelle/HOL workloads, performance
tuning. Performance target: **within 3× of upstream PolyML** on the
HOL/Isabelle benchmark suite (loose, since Cranelift's optimiser is
different from PolyML's). Tighter targets are Stage 3.

### Total Stage 2 (pessimistic)

| Phase | Estimate |
|---|---|
| Monday milestone | 7 weeks |
| 2.1 Interpreter port + bootstrap loading | 6 weeks |
| 2.2 Cranelift backend (x86_64) | 8 weeks |
| 2.3 Real GC | 6 weeks |
| 2.4 Concurrency | 3 weeks |
| 2.5 aarch64 target | 4 weeks |
| 2.6 macOS support | 4 weeks |
| 2.7 Portable image format (`bicimage`) | 6 weeks |
| 2.8 Hardening | 8+ weeks |
| **Total** | **~52 weeks ≈ 1 year** for one engineer |

Order is mostly sequential. Possible overlap: 2.5 (aarch64) and 2.6
(macOS) — different concerns, low coupling. 2.7 (bicimage) needs 2.2
done. 2.8 is continuous from 2.3 onwards.

---

## 3. Stage 3 and beyond (sketch)

- **Parallel GC**: port `gctaskfarm` + the work-stealing mark stacks
- **32-in-64 mode**: revisit compressed pointers
- **riscv64 target**: third arch; lights up if Stage 2 lands cleanly
- **32-bit native targets**: only if there's user demand
- **Save state / module system**: as a layer over `bicimage`
- **Debugger**, **profiler**: out of scope for Stage 2
- **Windows support**: explicit non-goal (no Windows hardware on hand)
- Tighter performance targets (closer to upstream parity)

---

## 4. Real vs. stubbed at each milestone

| Component | Monday | 2.1 | 2.2 | 2.3 | 2.4 | 2.5 | 2.6 | 2.7 |
|---|---|---|---|---|---|---|---|---|
| Heap-image loader | pexport | pexport | pexport | pexport | pexport | pexport | pexport | bicimage |
| Native code source | upstream | interp | Cranelift | " | " | + arm64 | + macOS | Cranelift |
| Interpreter | absent | real | real | real | real | real | real | real |
| GC | crash on OOM | crash | crash | real | real | real | real | real |
| Threading | 1 thread | 1 | 1 | 1 | many | many | many | many |
| Arch | host (Linux) | x86_64 | x86_64 | x86_64 | x86_64 | + arm64 | + macOS | all |
| Exceptions | none | basic | basic | basic | basic | basic | basic | basic |
| FFI | hardcoded | minimal | basic | basic | basic | basic | basic | basic |

---

## 5. Toolchain & licensing — locked

- **Rust toolchain**: rustup-managed. Current stable is **1.95.0** as
  of 2026-05-15 (rustup updated this session). A `rust-toolchain.toml`
  at the repo root pins stable; we re-pin when we want a newer one.
- **Rust edition**: 2024 (current stable). MSRV-pin via
  `rust-version` in `Cargo.toml` once we know Cranelift 0.131's actual
  floor.
- **Cranelift version**: pin to **0.131** family (current stable, April
  2026). Track 0.132 when it lands; don't track `main`.
- **License of `polyml-rs` crates**: dual **MIT / Apache-2.0** (Rust
  ecosystem norm; compatible with Cranelift's Apache-2.0-LLVM-exception).
- **Bootstrap image**: NOT vendored. The seed `bootstrap64.txt` lives
  in a separate sibling crate `polyml-bootstrap`, LGPL-2.1 licensed,
  consumed at runtime by `polyml-rs`. `polyml-rs` itself stays
  permissive. Final binary distributions that bundle them together
  comply with LGPL §5 (allow relinking).

---

## 6. Open questions — resolved (Stage 1 closeout)

| # | Question | Decision |
|---|---|---|
| 1 | Ambition | **Production replacement** for upstream PolyML |
| 2 | Licensing | Permissive `polyml-rs` + isolated LGPL bootstrap crate |
| 3 | Arch priority | **x86_64 → aarch64 → macOS → riscv64** (riscv64 is Stage 3) |
| 4 | 32-in-64 in Stage 2 | **Deferred to Stage 3** |
| 5 | Save-state compat | (not asked) — assume new format only; revisit if needed |
| 6 | Bootstrap-from-Rust priority | **Use our own** — interpreter port is Phase 2.1, *before* Cranelift |
| 7 | Cranelift fork vs upstream | Default to contributing upstream; fork only as last resort |
| 8 | Windows/macOS | **Linux first, then macOS. No Windows.** |
| 9 | Performance target | **Within 3× of upstream** on HOL/Isabelle (loose Stage-2 target) |

---

## 7. First Stage-2 action items (the first PRs after Stage 1)

In order. Each is a small enough chunk to be a single PR / merge unit.

1. **Repo scaffolding**: cargo workspace with `polyml-runtime`,
   `polyml-codegen-cl` (Cranelift backend), `polyml-image` (image
   format), `polyml-interpreter` (bytecode interpreter), `polyml-bin`
   (final binary), `polyml-bootstrap` (LGPL sidecar, bootstrap image).
   `rust-toolchain.toml` pins stable 1.95. `Cargo.toml` pins Cranelift
   0.131.
2. **Vendor PolyML for the Monday demo only**: an `xtask` invokes
   upstream `poly` to compile a fixture SML program to a pexport image
   into `target/fixtures/hello.pexport`. **This is a temporary crutch**;
   it goes away after Phase 2.1.
3. **pexport reader**: parse the existing text format, build an
   in-memory object graph. Check round-trip via a re-serializer.
4. **Stub TaskData + MemMgr**: minimum to allocate a permanent space
   and place the loaded objects in it.
5. **Hello-world execution** (Monday milestone target): trampoline
   into the root function; the single RTS callback (`writeString`) is
   a hardcoded Rust function.

That's the Monday milestone. Phase 2.1 (interpreter port) starts
immediately after — and once Phase 2.1 is done, action item 2 (the
upstream-poly xtask) is *deleted*, replaced by a Rust-only fixture
build that runs the SML compiler in our interpreter.
