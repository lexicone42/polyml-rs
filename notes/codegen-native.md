# PolyML Native Codegen Architecture Survey

## 1. Module Layering: The Codegen Pipeline

The native code generation pipeline follows a functor composition pattern in `mlsource/MLCompiler/CodeTree/`:

```
BackendIntermediateCode (BIC IR)
    ↓
X86CodetreeToICode / Arm64CodetreeToICode (functor entry point)
    ↓
X86ICode / Arm64ICode (abstract machine IR with pseudo-registers, preg)
    ↓
X86ICodeTransform / Arm64ICodeTransform (optimizations + register allocation)
    ├─ ICodeIdentify (liveness analysis)
    ├─ ICodeConflicts (conflict set computation)
    ├─ AllocateRegisters (linear scan or coloring)
    ├─ ICodeOptimise (peephole)
    └─ PushRegisters (callee-save handling)
    ↓
X86ICodeToX86Code / Arm64ICodeToArm64Code (lowering to architecture ops)
    ↓
X86OutputCode / Arm64Assembly (instruction encoding + output)
    ↓
CodeArray (byteVec → codeVec; constant pool insertion)
    ↓
Raw bytes in code object with GC-visible constant area

```

**Key binding files** show the composition:
- `X86Code/ml_bind.ML` (lines 18-120): stages X86 pipeline from CodetreeToICode → OutputCode → Optimise → ForeignCall → ICode → ICodeGenerate
- `Arm64Code/ml_bind.ML` (lines 18-113): analogous for Arm64, adds Assembly → PreAssembly layer
- `ByteCode/ml_bind.ML` (lines 20-34): interpreted path bypasses native codegen entirely

**Entry point signature**: `GENCODE.sig` lines 18-42 defines `gencodeLambda: bicLambdaForm * universal list * closureRef -> unit`. This is implemented by the final functor result, always called `X86Code` or `Arm64Code` after architecture selection at module load time (set by `GCode.x86_64.ML`, `GCode.arm64.ML`, etc., which alias the concrete module).

---

## 2. Instruction Selection Style

PolyML uses **tree pattern matching with macro expansion** in a two-layer intermediate:

**Layer 1: BIC IR → ICode (instruction selection)**  
`X86CodetreeToICode.ML` lines 113–end implements `codeFunctionToX86` functor that pattern-matches on `backendIC` constructors. Example from line 113:

```sml
fun codeFunctionToX86({body, localCount, name, argTypes, resultType=fnResultType, closure, ...}:bicLambdaForm, ...) = ...
```

Each `BIC*` constructor maps to one or more intermediate operations. The BIC IR has ~20 constructors (BACKENDINTERMEDIATECODE.sig lines 32-99):
- `BICConstnt` → `LoadArgument` (constant load)
- `BICEval` (function call) → `FunctionCall` or `TailRecursiveCall`
- `BICBinary`/`BICUnary` → arithmetic ops
- `BICCond` → conditional branch with two branches
- `BICLoop`/`BICBeginLoop` → loop constructs with jump-back
- `BICRaise`/`BICHandle` → exception mechanisms

**Layer 2: ICode → architecture code (lowering)**  
`X86ICodeToX86Code.ML` converts preg-based ICode (X86ICODE.sig) into `X86CODE` operations (X86CODE.sig lines 105–170, ~60 operations):
- `LoadArgument` → `Move`, `LoadAddress`
- `FunctionCall` → `CallAddress`, stack setup
- Register allocation resolves preg → concrete register
- Stack locations become memory addresses

Each architecture implements this differently: X86 uses x87/SSE2 floating point, Arm64 uses V-registers, etc.

---

## 3. Register Allocation

**Linear scan based with conflict sets** (not graph coloring). Two key modules:

**X86AllocateRegisters** (`X86Code/X86AllocateRegisters.ML` lines 18–100+):
- Takes extended basic blocks with pseudo-register conflict information
- Returns `AllocateSuccess of reg vector` or `AllocateFailure` if spills needed
- Uses "hints" (line 75–93) to preferentially assign registers: `realHints` for forced constraints (e.g., shift count must be in ECX), `sourceRegs`/`destinationRegs` for move coalescing
- Available registers per architecture (line 37–45):
  - 32-bit: `[edi, esi, edx, ecx, ebx, eax]` (6 regs)
  - 64-bit: adds `[r14, r13, r12, r11, r10, r9, r8]` (13 regs)
- FP registers: SSE2 mode uses `[xmm5..xmm0]` (6 regs); X87 mode only `[fp0]` (1 reg)

**Reference computation** (X86IDENTIFYREFERENCES.sig, X86ICodeIdentifyReferences.ML): walks ICode to compute liveness and conflict sets. Conflicts identify which pregs cannot occupy the same physical register (live simultaneously or forced constraints like shift operands).

Stack allocation for spilled values happens in the transform phase before code generation.

---

## 4. Calling Convention

**X86 native 64-bit ABI:**
- **GP arg registers**: rax, rbx, r8–r10 (first 5 args; see X86CodetreeToICode.ML line 40)
- **FP arg registers**: xmm0–xmm2 for double/float args (line 44)
- **Result**: eax/rax (GP) or XMM0 (FP)
- **Stack**: args beyond registers pushed right-to-left; return address at [rsp]

**Arm64 ABI:**
- **GP args**: X0–X7 (8 regs)
- **FP args**: V0–V7 (8 SIMD regs, used for float/double)
- **Result**: X0 (GP) or V0 (FP)

**Task/ThreadData pointer (ML heap metadata):**
- Stored in **TaskData register** (architecture-specific):
  - X86: typically in a memory cell accessed via `memRegThreadSelf` (X86CODE.sig line 187, mapped to a word in the runtime's "memory registers" block)
  - Arm64: similar indirection via stack/runtime state
- Set at function entry; not generally passed in a register (unlike, e.g., Go's goroutine-local storage)

**Tail calls** (BICLoop/BICBeginLoop):
- Implemented as `TailRecursiveCall` in ICode (X86ICODE.sig line 168–171)
- Adjusts stack pointer to remove old args and return address, then jumps (not calls) to loop entry
- Avoids stack buildup in recursive loops

---

## 5. GC Integration & Safepoints

**Safepoint placement:**
- Before any `AllocateMemoryOperation` (X86ICODE.sig line 177): triggers potential GC
- At function entry (to check stack limit and save callee-save regs)
- `PushExceptionHandler` / `PopExceptionHandler` (lines 227–230): GC may run in handler setup

**Stack maps:**
- **Not explicitly generated** as separate metadata; instead, the GC scans the **code object's constant area** which references all live heap addresses
- Each code object has format: `[length_word | code_bytes... | constant_pool]`
  - Last word: offset to constants section (machine_dep.h convention)
  - Constants include: closure references, large-word constants, addresses of other code objects
  - GC walks code objects and updates references in-place during collection

**Allocation fast path:**
- `AllocateMemoryOperation` (X86ICodeToX86Code.ML, line 177 in sig) emits either:
  - Fast path: bump-allocate from heap pointer (if size known and small)
  - Slow path: `CallRTS` to PolyCAlloc (or equivalent), which does GC if needed
- Save registers list (X86ICODE.sig line 177: `saveRegs: preg list`) tells GC which regs contain heap pointers requiring update

**GC-safe points are implicit**: any runtime call is a safepoint; the RTS walks the ML stack frame to find heap references.

---

## 6. Closure Representation

**Closure layout** (in ML heap):
- A closure is a heap object (mutable) with:
  - Length word (with flags: F_closure tag)
  - Array of pointers to code objects and free variables
  - Example: closure for `fn (x) => fn (y) => x + y` captures `x`

**Per-architecture differences:**
- **32-bit**: pointer size = 1 word (4 bytes)
- **64-bit**: pointer size = 1 word (8 bytes)
- **32-in-64** (ObjectId mode): pointers are 4-byte object IDs; address computation requires indirection through object table

Each architecture's ICode (X86ICODE.sig, ARM64ICODE.sig) has a `closure: bicLoadForm list` field specifying free variables. The codegen:
1. Allocates or receives closure as a pointer
2. Emits loads for each free variable from closure at compile time
3. On tail call, may pass updated closure to recursive function

---

## 7. Constant Pool & Code Object Layout

**Layout (from machine_dep.h convention, implemented in CodeArray.ML):**

```
+————————————————————————————+
| Length word (with flags)   | ← object header, F_code | F_closure bit set
+————————————————————————————+
| Machine code (variable)    |
| ...                        |
+————————————————————————————+
| Constant pool              | ← offsets, addresses, floats
| ...                        |
+————————————————————————————+
| Offset to constants (final)| ← at codeVecAddr + codeVecLength - wordSize
+————————————————————————————+
```

**Construction**:
- `CodetreeCodegenConstantFunctions.ML` (lines 66–73): code-generates functions with empty closures immediately to get code addresses for embedding as constants
- `X86OutputCode.ML`, `Arm64Assembly.ML`: emit code bytes into a mutable byteVec
- `CodeArray.ML` (lines 57–69, 129–138): `byteVecToCodeVec` copies mutable byteVec into immutable code object; `codeVecPutConstant` (lines 116–127) handles relocatable constants
  - `ConstAbsolute`: 64-bit address (used for large-word constants)
  - `ConstX86Relative`: RIP-relative for position-independent code (X86 64-bit)
  - `ConstArm64AdrpLdr*`: Arm64-specific; ADRP + LDR pair for address loads

**Constant pool contents:**
- Addresses of other code objects (for indirect calls or closure references)
- Large floating-point constants (8/16 bytes)
- Large integer constants (outside immediate-encode range)
- Relocations (if cross-module calls)

---

## 8. FOREIGNCALL.sig Interface

**Location**: `mlsource/MLCompiler/FOREIGNCALL.sig` (lines 18–35)

**Fast-call interface** (for simple C functions):
```sml
val rtsCallFast: string * int * universal list -> Address.machineWord
val rtsCallFastRealtoReal: string * universal list -> Address.machineWord
```

These JIT-compile C wrappers on first call, caching them. Used for:
- `FloatAbs`, `FloatFloor`, single arg/result functions
- Returns a code object address that can be called

**General FFI**:
```sml
type abi and cType
val foreignCall: abi * cType list * cType -> Address.machineWord
val buildCallBack: abi * cType list * cType -> Address.machineWord
```

- Per-architecture implementation: `X86ForeignCall.ML` (X86Code subdir), `Arm64ForeignCall.sml` (Arm64Code subdir)
- `foreignCall` emits a wrapper that:
  - Marshals ML arguments (tagged words → C values)
  - Calls the external C function
  - Marshals return value back to ML
  - Returns code object address
- `buildCallBack` creates the inverse (C → ML)

---

## 9. Cranelift Fit: Impedance Mismatches

**What maps cleanly:**
1. BIC IR → Cranelift IR: one-to-one for most ops (binary ops, loads, stores, calls)
2. Register allocation: Cranelift's regalloc can replace PolyML's linear scan
3. Instruction selection: Cranelift's lowering handles x86/arm64 differences

**What doesn't map 1:1:**

1. **Pseudo-register to physical register mapping**:
   - PolyML uses an extra abstraction layer (`preg`, `pregOrZero`) with properties and stack locations. Cranelift's IR is closer to SSA with unlimited virtuals. The extra layer could simplify to direct Cranelift IR.

2. **Tail-recursive calls & loop control**:
   - PolyML's `BICLoop`/`BICBeginLoop` are syntactic loop constructs that must lower to jump (not call). Cranelift uses standard function calls; tail recursion requires either:
     - Marking calls with a tail-call hint (Cranelift has `call_indirect_table` but not explicit tail-call lowering for all cases)
     - Or keeping the current loop-lowering pass before Cranelift

3. **Exception handling**:
   - PolyML uses explicit `PushExceptionHandler`/`PopExceptionHandler`/`BeginHandler` ICode ops managing a linked-list handler stack (implicit in registers/memory)
   - Cranelift uses WebAssembly-style `block`/`loop`/`br_on_exn`, or delegates to platform unwinding (DWARF/Windows EH)
   - Adapting requires either:
     - Wrapping Cranelift's EH in a custom handler-stack lowering pass
     - Or using Cranelift's native mechanism and updating GC safepoint scanning

4. **Memory allocation fast-path**:
   - PolyML bakes bump-allocation inline with a check. Cranelift doesn't directly expose "check + alloc" as a single operation.
   - Solution: lower `AllocateMemoryOperation` to Cranelift IR that includes the bounds check, then let Cranelift's lowering emit the fast path or a call.

5. **Closure & TaskData access**:
   - PolyML accesses the ML heap's TaskData record via indirect reads from a memory-register cell. Cranelift would need similar, but its ABI handling assumes traditional calling conventions. Custom intrinsics may be needed.

6. **Constant pool relocation types**:
   - PolyML uses `ConstAbsolute`, `ConstX86Relative`, `ConstArm64Adrp*`. Cranelift's relocations are simpler (direct references, GOT entries, TLS). May require custom fixup pass.

---

## 10. Where Cranelift Slots In Cleanly

**Minimum viable integration:**

Implement `gencodeLambda` (GENCODE.sig line 30) as:

```sml
fun gencodeLambda(bicLambdaForm, debugSwitches, resultClosure) =
  let
    (* 1. Conversion: BIC IR → Cranelift IR *)
    val (cranelift_func, const_refs) = bicToCliffir(bicLambda)
    
    (* 2. Optimization: run Cranelift's builtin passes *)
    val optimized = Cranelift.optimize(cranelift_func)
    
    (* 3. Register allocation + code generation: Cranelift's regalloc + lowering *)
    val code_bytes = Cranelift.compile(optimized)
    
    (* 4. Emit into code object with constant pool *)
    val code_obj = CodeArray.byteVecToCodeVec(code_bytes, resultClosure)
    
    (* 5. Install constants (relocations) *)
    val () = installConstants(code_obj, const_refs)
    
    (* 6. Lock for GC *)
    val () = CodeArray.codeVecLock(code_obj, resultClosure)
  in
    ()
  end
```

**Key contract with GC:**
- Code object format: `[length | code | constants | offset_to_constants]`
- All `const_refs` must appear in the constants section
- GC scans constants area and updates heap pointers in-place
- No frame maps needed if constants are self-identifying (tagged)

**Architecture independence:**
- Cranelift targets multiple ISAs; select via ABI/ISA parameter at functor instantiation
- Current per-arch functors (X86*, Arm64*) become parameter-driven, or kept as thin wrappers around the Cranelift path

---

## File Structure Summary

| File | Role |
|------|------|
| `BACKENDINTERMEDIATECODE.sig` | ~20 IR constructors; input to codegen |
| `GENCODE.sig` | Codegen interface: `gencodeLambda` |
| `CODEARRAY.sig` | Code object allocation & constant insertion |
| `X86Code/X86CodetreeToICode.ML` | BIC → X86 ICode instruction selection |
| `X86Code/X86ICODE.sig` | Abstract machine IR with pregs |
| `X86Code/X86AllocateRegisters.ML` | Linear scan regalloc |
| `X86Code/X86ICodeTransform.ML` | Transforms: liveness, regalloc, optimization |
| `X86Code/X86ICodeToX86Code.ML` | ICode → X86 ops lowering |
| `X86Code/X86OutputCode.ML` | Instruction encoding & byte emission |
| `Arm64Code/Arm64*.ML` | Analogous for Arm64 |
| `ByteCode/IntGCode.ML` | Bytecode interpreter path |
| `CodetreeCodegenConstantFunctions.ML` | Eager codegen for closure-free functions |
| `mlsource/MLCompiler/FOREIGNCALL.sig` | C interop interface |
| `RootX86.ML`, `RootArm64.ML` | Top-level module composition & use files |

---

## Observations

1. **The per-architecture split is *deep***: X86Code and Arm64Code each reimplement ICode, register allocation, code gen, and output. There's opportunity for a unified Cranelift-based path that makes architecture selection a parameter rather than duplicated code.

2. **Exception handling is non-standard**: PolyML's explicit handler-stack pushes/pops will require careful mapping to Cranelift's EH mechanism (or a custom pass to lower them before Cranelift).

3. **Closure-free function eager codegen** (CodetreeCodegenConstantFunctions.ML) is clever for avoiding allocations, but Cranelift would need the same optimization applied at the frontend or as a separate pass.

4. **The constant pool is GC-critical**: the offset-to-constants word at the end is a PolyML convention that must be preserved in any rewrite, or the GC scanning logic must change in lockstep.

