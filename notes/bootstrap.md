# PolyML bootstrap

Read in conjunction with `notes/heap-image.md` (pexport format) and
`notes/codegen-native.md` (backends).

## The mystery: how do you build a self-hosted compiler on a new arch?

PolyML's compiler is itself in SML. To bootstrap on a new architecture
(say a new Arm64-32 port), you'd seem to need a working SML compiler that
already runs there, which is what you're trying to build. PolyML has an
elegant solution: a portable, *interpreted* seed image.

## The seed: `bootstrap/bootstrap64.txt`

There are exactly two seed images in the repo:

- `bootstrap/bootstrap64.txt` (1.8 MB)  ← used for any 64-bit target
- `bootstrap/bootstrap32.txt` (1.4 MB)  ← used for any 32-bit target

The selection is in `vendor/polyml/Makefile.am:21-25`:

```
if BOOT64
POLYIMPORT = $(srcdir)/bootstrap/bootstrap64.txt
else
POLYIMPORT = $(srcdir)/bootstrap/bootstrap32.txt
endif
```

Note: **no per-architecture** seed.  One 64-bit seed works for x86_64
*and* aarch64 *and* riscv64.

## How it's portable: it's bytecode

The seed file format is described in `notes/heap-image.md`. Its header
encodes the source architecture:

```
Objects	22588
Root	8390 I 8
```

`I 8` = interpreted backend, 8-byte words. The runtime reads this in
`vendor/polyml/libpolyml/pexport.cpp:539-550`:

```cpp
// Older versions did not have the architecture and word length.
if (ch != '\r' && ch != '\n')
{
    unsigned wordLength;
    while (ch == ' ' || ch == '\t') ch = getc(f);
    char arch = ch;
    ...
    // If we're booting a native code version from interpreted
    // code we have to interpret.
    machineDependent->SetBootArchitecture(arch, wordLength);
}
```

Even when `machineDependent` is the native x86_64 module, if the seed
says `'I'`, the runtime **falls back to the interpreter** for the bootstrap
phase.  The bytecode interpreter is `libpolyml/interpreter.cpp` /
`bytecode.cpp` — separate from native code.

## What's in the seed

Sampling record types in `bootstrap64.txt` (counting `^[0-9]+:[A-Z]` prefixes):

| Type | Count | Meaning (from `pexport.cpp` reader) |
|------|-------|--------------------------------------|
| O    | 5195  | Ordinary word-containing object |
| M    | 4688  | Mutable variant of `O` |
| C    | 4513  | Closure (32-in-64; pointer to code + closure data) |
| F    | 4436  | Code/function object |
| S    | 3750  | String / byte object (different from B?) |
| B    | 6     | Byte object |

The seed contains the entire compiler *as the bytecode interpreter sees it*.
That's why it's small (1.8 MB): it's interpreter ops, not x86 instructions.

## The pipeline (`Makefile.am:78-83` and `bootstrap/Stage1.sml`)

```
polyimport (tiny C, ~10 lines)
   │
   │  reads bootstrap64.txt, sets up interpreter,
   │  then reads Stage1.sml from stdin
   ▼
Stage1.sml      ── runs in interpreter
   │   Bootstrap.use "basis/build.sml"
   │   (compile the SML basis library)
   │   PolyML.use "bootstrap/Stage2.sml"
   ▼
Stage2..6.sml   ── progressively rebuild the compiler
                   using its native codegen for the target
   ▼
Stage7.sml      ── final stage; exports `polyexport.o`
   │
   ▼
polyexport.o    ── linkable object containing the native
                   compiler image for *this* target
   │
   ▼  linked with libpolyml + libpolymain
poly binary     ── the final native compiler
```

Stages 2–7 are small (28–65 lines each) — they're driver scripts that
`use` the right combination of compiler-source files for the target.

## Top-level project roots

`RootX86.ML`, `RootArm64.ML`, `RootInterpreted.ML` are the per-target lists
of which source files compose the compiler. They select different `GCode.*`
files. So "porting to a new arch" really means writing a new `GCode.<arch>.ML`
+ corresponding `<Arch>Code/` subdirectory + a `Root<Arch>.ML` and updating
the Makefile to pick it up.

## Implications for `polyml-rs`

1. **We need a working bytecode interpreter** in the new Rust runtime to
   load the existing seed (or any future portable seed).
   - Option A: port `interpreter.cpp` / `bytecode.cpp` to Rust verbatim.
   - Option B: skip the interpreter; require an x86 / arm64 native compiler
     to already exist (i.e. use upstream poly to build a heap image first,
     then port from there). Tempting for early milestones but punts on the
     real portability story.

2. **The seed is *the* bootstrap dependency**. If our Rust runtime can load
   the existing `bootstrap64.txt`, we automatically get the entire SML
   compiler at our disposal — no need to re-implement parsing, typechecking,
   IR construction, optimisation. We only have to plug in a new codegen
   backend (Cranelift) for the final stages.

3. **The bootstrap-from-interpreter pattern is reusable**. For our
   architecture-portable heap-image goal, we can adopt the same pattern:
   ship a portable image as bytecode (or BIC IR), have it interpreted (or
   JIT-compiled by Cranelift) at load on the target. Heap images are no
   longer cross-arch; they're cross-arch portable *because they contain a
   compileable representation*, not native code.

4. **Open question**: does the existing interpreter share enough invariants
   with our native runtime that we can run both side-by-side, or does
   adding Cranelift force changes to the calling convention / object layout
   that break interpreter compatibility? Need to read `interpreter.cpp`
   more carefully in Stage 2 before committing to "just port the interpreter".

## References

- `vendor/polyml/bootstrap/Stage1.sml:21-28` (entry)
- `vendor/polyml/bootstrap/bootstrap64.txt:1-2` (header format)
- `vendor/polyml/libpolyml/pexport.cpp:303-315` (header writer)
- `vendor/polyml/libpolyml/pexport.cpp:520-550` (header reader)
- `vendor/polyml/Makefile.am:21-25, 78-83` (build pipeline)
- `vendor/polyml/polyimport.c` (the tiny seed loader)
- `vendor/polyml/RootX86.ML`, `RootArm64.ML`, `RootInterpreted.ML` (per-target roots)
- `vendor/polyml/libpolyml/interpreter.cpp` (the interpreter itself — not yet read)
