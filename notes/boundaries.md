# Boundaries

The three interfaces a Rust+Cranelift rewrite must respect (or
deliberately redesign). All file refs are relative to `vendor/polyml/`.

---

## 1. Runtime ↔ compiled-code interface

This is the contract between native code emitted by the codegen and
`libpolyml`.  It's the *minimum* the new Rust runtime must expose.

### 1.1 Per-thread state: `TaskData`

Defined in `libpolyml/processes.h:99-360` (base) and specialised per
arch (`x86_dep.cpp`, `arm64.cpp`). Each ML thread = one OS thread, with
a `TaskData` pinned to it.

Critical fields visible to compiled code:

| Field | Type | Purpose | File |
|-------|------|---------|------|
| `allocPointer` | `PolyWord*` | Bump-down allocation cursor | `processes.h:141` |
| `allocLimit`   | `PolyWord*` | Lower bound of current alloc region | `processes.h:142` |
| `stackLimit`   | `stackItem*` | Low-water mark for the ML stack | (`assemblyInterface`) |
| `stackPtr`     | `stackItem*` | Current ML stack pointer | (`assemblyInterface`) |
| `assemblyInterface.heapOverFlowCall` | `byte*` | Trampoline addr | `x86_dep.cpp:160` |
| `handlerRegister` | exception chain head | On-stack handler list | (per arch) |

The Arm64 backend assigns dedicated registers to these (per the
scheduler/FFI survey):

- **X26** — pointer to `AssemblyArgs` (most of the above)
- **X27** — heap allocation pointer (`allocPointer`)
- **X28** — ML stack pointer (`stackPtr`)

x86_64 uses analogous fixed registers; see `x86_dep.cpp:160-200`.

### 1.2 Safepoint mechanism — exactly two trap kinds

There is **no periodic safepoint poll**.  All thread-stopping is driven
through these two checks emitted by the codegen:

1. **Allocation-limit check** at every alloc site
   ```
   sub  Xnew, allocPointer, #size       ; compute new alloc ptr
   cmp  Xnew, allocLimit                ; would we cross?
   b.lo  heapOverFlowCall_trampoline    ; trap
   mov  allocPointer, Xnew              ; commit
   ```
   The trampoline saves regs, transfers to C++, and on return either
   re-allocates (after GC or new region) or raises an exception.
   Reference: `x86_dep.cpp:906-934`, `arm64.cpp:787-810`.

2. **Stack-limit check** at every function prologue
   ```
   cmp  stackPtr, stackLimit
   b.lo  stack_overflow_trampoline
   ```
   When the runtime wants to interrupt a thread, it sets
   `stackLimit = stack->top - 1` from *another* thread
   (`arm64.cpp:775-784`):
   ```cpp
   void Arm64TaskData::InterruptCode() {
       PLocker l(&interruptLock);
       if (stack != 0)
           assemblyInterface.stackLimit = (stackItem*)(stack->top - 1);
   }
   ```
   This guarantees the next prologue trap, even in code that doesn't
   allocate.

So **the codegen MUST emit both of these checks** for the runtime to be
able to interrupt threads at all.  Together they are the safepoints.

### 1.3 GC roots from compiled code

When a thread is at a safepoint trap, the GC walks its stack and
registers.  Stack walking is currently *convention-based*: each `GCode`
backend emits frames with a known shape, and the matching
`<Arch>TaskData::ScanStackAddress` knows that shape
(`arm64.cpp:353-360`).  There are **no stack maps** in the modern
mid-90s sense; the runtime knows what's a pointer because (a) tagged
ints have bottom bit set, (b) frame-stored values are at known
positions, (c) the length-word of each object carries type bits.

**Consequence for Cranelift:** the runtime cannot infer the live-set
of arbitrary Cranelift-allocated frames.  Either:
- Cranelift emits **stack maps** at safepoints (`enable_safepoints =
  true`), or
- The codegen enforces a constrained frame convention that the runtime
  can interpret directly.

### 1.4 RTS call ABI

Compiled code calls into the runtime for arbitrary-precision
arithmetic, string ops, allocation overflow, signals, FFI, etc. The
convention (from scheduler/FFI survey):

- Caller passes the thread ID in **X0** (Arm64) or a fixed reg (x86)
- C++ side uses the `SaveVec` to manage GC roots during native execution
- Return-value convention follows the platform C ABI

Each RTS entry point is named (`PolyThreadInterruptThread`, etc.) and
registered in a table (`processes.cpp:172`).  The compiler emits direct
calls to these by name; the linker resolves them.

### 1.5 Code-object layout

Every code object has a length word + (mostly) executable bytes + a
constant pool. From `machine_dep.h:61-67`:

```
[length-word][native code bytes ............][constants ...][last_word]
                                                            ^^^^^^^^^^
                                              negative byte offset to constants
```

The runtime's `GetConstSegmentForCode` walks back via the last word to
find constants for GC scanning. The constants area carries embedded
pointers to other heap objects and code — these are GC roots.

**Consequence for Cranelift:** when Cranelift emits a function, the
wrapper must:
1. Lay the code into a PolyML code object (length word, body)
2. Append a constant table with relocations pointing into other heap
   data
3. Write the trailing offset

### 1.6 Exception model

On-stack handler chain (not zero-cost tables, not libunwind). From the
scheduler/FFI survey + `arm64.cpp`:

- `BICHandle` lowers to: push handler frame, run protected expression,
  pop handler frame
- `BICRaise` walks the handler chain, restoring SP & resuming at the
  matching handler PC
- The chain head lives in `handlerRegister` (in `assemblyInterface`)

**Consequence:** Cranelift will *not* use platform unwinding for ML
exceptions. It will emit handler push/pop and a small inline raise.
Cranelift's existing exception support (table-based, platform unwind)
is the wrong shape.

### 1.7 FFI

Bare `dlopen`/`LoadLibrary` — no libffi (per scheduler/FFI survey).
Callbacks need compiler-generated wrappers. Static calls go through a
codegen-emitted thunk per signature (`FOREIGNCALL.sig` is the
SML-level interface).

---

## 2. Compiler ↔ codegen interface

This is the seam where Cranelift plugs in.  It's gloriously narrow.

### 2.1 The signature: `GENCODE.sig`

`mlsource/MLCompiler/CodeTree/GENCODE.sig` is exactly **40 lines**.
The contract:

```sml
signature GENCODE = sig
    type backendIC and argumentType and machineWord and bicLoadForm
    type closureRef

    type bicLambdaForm = {
        body          : backendIC,
        name          : string,
        closure       : bicLoadForm list,
        argTypes      : argumentType list,
        resultType    : argumentType,
        localCount    : int
    }
    val gencodeLambda: bicLambdaForm * Universal.universal list
                       * closureRef -> unit

    structure Foreign: FOREIGNCALL
    ...
end
```

**One function plus an FFI sub-structure.** That's the whole interface
the existing X86/Arm64/Bytecode backends implement.

### 2.2 The IR: `backendIC` (BIC)

Defined in `BACKENDINTERMEDIATECODE.sig`.  Approximately 20
constructors:

| Op | Purpose |
|----|---------|
| `BICNewenv` | Block of bindings + body |
| `BICConstnt` | Load constant |
| `BICExtract` | Load local/arg/closure-slot |
| `BICField` | Tuple/record field load |
| `BICEval` | Function application |
| `BICNullary/Unary/Binary` | Built-in primitives |
| `BICArbitrary` | Arith with arbitrary-precision fallback |
| `BICLambda` | Inner λ |
| `BICCond` | If-then-else |
| `BICCase` | Multi-way switch |
| `BICBeginLoop` / `BICLoop` | Tail-recursive inline loop |
| `BICRaise` | Raise exception |
| `BICHandle` | Catch exception |
| `BICTuple` | Tuple construction |
| `BICSetContainer` / `BICLoadContainer` | Stack tuples |
| `BICTagTest` | Tag check |
| `BICLoadOperation` / `BICStoreOperation` | Memory ops |
| `BICBlockOperation` | Byte-block ops |
| `BICAllocateWordMemory` | Heap alloc |

Argument types:

```sml
datatype argumentType =
    GeneralType                  (* any tagged ML value *)
|   DoubleFloatType              (* unboxed float64 *)
|   SingleFloatType              (* unboxed float32 *)
|   ContainerType of int         (* stack tuple of N words *)
```

### 2.3 Two notable IR features

- **`BICArbitrary`** has four sub-trees: a tagged-int fast condition,
  arg1, arg2, and a `longCall` fallback. Codegen emits a branch: if
  both are tagged and no overflow, do the unboxed op; else call the
  arbitrary-precision routine. The new backend must support both arms.
- **`BICBeginLoop` / `BICLoop`** are explicit tail-recursive loops —
  these are sources of *guaranteed* tail-call edges and lower to plain
  jumps.  Other tail-call edges come from `BICEval` in tail position;
  those need real tail-call codegen.

### 2.4 What "lowering" looks like today

(Per the codegen survey.)

```
BackendIntermediateCode  (backendIC, ~20 constructors)
        │
        ▼  per-arch CodetreeToICode
ICode (pseudo-register IR, ~40 constructors)
        │
        ▼  transform/regalloc (linear scan + hints)
Arch-specific ICode (~60 ops)
        │
        ▼  lowering + emission
Bytes written via CodeArray
        │
        ▼
PolyML code object: [length | code | constants | offset]
```

For our Cranelift backend the path collapses to:

```
backendIC
        │
        ▼  bic_to_clif (new code)
Cranelift IR
        │
        ▼  cranelift-codegen
Machine bytes
        │
        ▼  wrap_into_polyml_code_object
PolyML code object
```

---

## 3. Heap-image format

(Full details in `notes/heap-image.md`.)

### 3.1 Two existing formats

| | Native object export | Portable (pexport) |
|---|---|---|
| File | `elfexport.cpp`, `machoexport.cpp`, `pecoffexport.cpp` | `pexport.cpp` |
| Output | ELF/Mach-O/COFF | Custom text format |
| Linkable | Yes (`polyexport.o`) | No (loaded by polyimport) |
| Used for | Final compiled `poly` binary | Bootstrap seed (`bootstrap64.txt`) |
| Cross-OS | No | Yes |
| Cross-arch | **No** | **No** (but see below) |

### 3.2 What in the image is architecture-dependent

(Listed bare; rationale in `notes/heap-image.md`.)

1. **Word size** — image header records 4 or 8 bytes (`Root ... I 8`)
2. **Endianness** — values written in native byte order
3. **Tagged-int range** — `MAXTAGGED` differs between 32 and 64 bits
4. **32-in-64 offsets** — pointer payload is `index = (addr -
   globalHeapBase) / POLYML32IN64`, only meaningful with the same
   layout at load
5. **Native machine code** in code-object bytes (architecture-specific
   instructions)
6. **Code-object constant-area offset** in the last word (depends on
   word size; the values are byte offsets)
7. **Architecture-specific relocations** in code objects (x86
   RIP-relative, Arm64 ADRP/LDR pairs, etc.)
8. **Arch byte in the pexport header** itself: `'I' / 'X' / 'A'`

### 3.3 The pexport architecture-portability trick

`pexport.cpp:308-315` writes:

```cpp
char arch = '?';
switch (machineDependent->MachineArchitecture()) {
case MA_Interpreted: arch = 'I'; break;
case MA_I386: case MA_X86_64: case MA_X86_64_32: arch = 'X'; break;
case MA_Arm64: case MA_Arm64_32:                arch = 'A'; break;
}
fprintf(exportFile, "Root\t%" PRI_SIZET " %c %u\n", ..., arch, wordLength);
```

When a *native* poly binary loads a pexport image whose header says
`'I'`, the comment at `pexport.cpp:547-549` says:

> *"If we're booting a native code version from interpreted code we have
> to interpret."*

So images compiled with the bytecode backend are loadable on any
target with matching word size, by falling back to the interpreter
for the bootstrap phase. This is how `bootstrap64.txt` works
(`notes/bootstrap.md`).

### 3.4 Implication for our portable heap image

The existing "portable" format is portable across OS only.  True
cross-arch portability needs one of:

- **A**: Ship BIC (backendIC IR) in the image; re-codegen at load.
  Most compact; requires the loader to include codegen.
- **B**: Ship Cranelift IR (CLIF). Lower-level but Cranelift-version
  coupled.
- **C**: Ship bytecode; interpret or JIT.  Existing pattern.
- **D**: Ship Cranelift's portable wasm/binaries. Largest but truly
  pre-compiled.

Recommendation in `notes/hard-problems.md`.

---

## 4. What the new Rust runtime must expose (minimal)

A checklist derived from the above:

- [ ] `TaskData` struct with: thread ID, allocPointer, allocLimit,
      stackLimit, stackPtr, handler chain head, exception packet slot,
      saved register set, the SaveVec
- [ ] Allocation trampoline (`heap_overflow_trap`) entered when
      `allocPointer < allocLimit`
- [ ] Stack-overflow trampoline entered when `stackPtr < stackLimit`
- [ ] `interrupt_thread(tid)` that poisons the target's `stackLimit`
- [ ] GC entry points: `full_gc`, `quick_gc`, with stop-the-world
      coordination
- [ ] Stack-scanning hook callable per-arch with a frame map or
      stack-map lookup
- [ ] Heap memory manager: permanent vs local vs code spaces, bitmaps
- [ ] Code-object allocator (writable then read-only flip)
- [ ] Exception raise / handler-frame walk
- [ ] RTS function table for compiler-emitted name resolution
- [ ] Heap-image loader: parse pexport-derived format, restore
      pointers, set boot architecture
- [ ] The save-state writer (round-trip)
- [ ] FFI: dlopen + a per-signature trampoline emitter
- [ ] Optional: bytecode interpreter (for bootstrap and cross-arch
      loading)

And what the codegen plug-in must implement:

- [ ] `gencode_lambda(lambda: bicLambdaForm, props, closure_ref)`
      that ingests BIC and emits a PolyML code object via Cranelift
- [ ] Stack-map emission at all alloc sites and function prologues
- [ ] Constant-table layout matching `machine_dep.h:GetConstSegmentForCode`
- [ ] Exception-handler-frame push/pop lowering for `BICHandle`
- [ ] `BICArbitrary` two-arm lowering
- [ ] Tail-call lowering for `BICLoop` and tail-position `BICEval`
- [ ] FFI codegen (`FOREIGNCALL` substructure)
