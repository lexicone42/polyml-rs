# PolyML Heap Image Format Analysis

## 1. Current Heap Image Layout, Byte-for-Byte

### High-Level Structure
PolyML's heap image is conceptually built from three main components:
- **Memory spaces**: Permanent immutable data, permanent mutable data, executable code, and local (garbage-collected) data
- **Objects**: PolyML heap objects with length words and payloads
- **Relocations**: Links between objects and machine-code constants

### On-Disk Format: Two Variants

PolyML supports two fundamentally different on-disk formats:

#### A. **Portable Format** (`pexport.cpp:269–339`)
A text-based format (arguably a debugging/interchange format):
```
Objects	<count>
Root	<index> <arch> <word_size>
<index>:<flags>O<length>|value,value,...
<index>:<flags>S<nbytes>|<hex_bytes>
<index>:<flags>F<const_count>,<code_bytes>|<code_hex>|<const0>,<const1>,...
<index>:<flags>B<nbytes>|<hex_bytes>
```
Where flags are modifiers: `M` (mutable), `N` (negative/high-bit-set), `V` (no-overwrite), `W` (weak reference).

Each line represents one object. Objects are indexed `0..N-1` in allocation order. Values reference other objects via `@<index>` or are tagged integers. Constants within code get inline relocations (`<offset>,<reloc_kind>,@<target>`).

**Portable format is NOT architecture-portable**: It encodes the architecture marker (X for x86, A for ARM) and word size (line 315: `fprintf(exportFile, "Root\t%" PRI_SIZET " %c %u\n", getIndex(rootFunction), arch, (unsigned)sizeof(PolyWord))`). The importer checks this (line 549: `machineDependent->SetBootArchitecture(arch, wordLength)`), but it requires recompilation if the target architecture differs.

#### B. **Native Object File Format** (ELF/Mach-O/COFF, via `elfexport.cpp`, `machoexport.cpp`, `pecoffexport.cpp`)
Embeds the heap in an executable's read-only and read-write sections. The loader (`mpoly.cpp`) extracts the memory table pointer from the binary symbol table or sections.

**Architecture-specific**: Uses processor-native relocation types (R_X86_64_64, R_AARCH64_ABS64, etc.; `scanaddrs.h:27–35`). These are concrete machine instructions, not portable.

### Memory Layout in Permanent Spaces

Permanent spaces contain objects contiguously with length words. Key structure (`memmgr.h:151–175`):
- `PermanentMemSpace::bottom`, `top`: Boundaries
- `PermanentMemSpace::topPointer`: During export, points to next free word in a growing export area
- `PermanentMemSpace::index`: 0-based space identifier
- `PermanentMemSpace::moduleIdentifier`: 128-bit hash (`struct _moduleId { uint32_t modA, modB }`) tying space to source module

**Object layout** (single object):
```
[PolyWord: length_word]  // High bits = flags, low bits = word count
[PolyWord: data[0]]
[PolyWord: data[1]]
...
[PolyWord: data[length-1]]
```

For code objects specifically, the constant area is either embedded or separate.

### Module Format (`modules.cpp:122–188`)

PolyML also has a binary **module** format (separate from saved state):
```
[Header]
  char[8]   "POLYMODU"
  uint32    version (=3)
  uint32    headerLength
  uint32    segmentDescrLength
  [offsets and counts]
  struct _moduleId thisModuleId, executableModId
  [string table offset/size]
  [dependency table offset/count]
  uintptr_t rootSegment, rootOffset

[Segment descriptors] ×N
  off_t     segmentData
  size_t    segmentSize
  off_t     relocations
  uint32    relocationCount
  uint32    relocationSize
  uint32    segmentFlags (MSF_WRITABLE, MSF_CODE, MSF_BYTES, etc.)
  uint32    segmentIndex
  struct _moduleId moduleIdentifier

[Relocations per segment]
  POLYUNSIGNED relocAddress      // Byte offset in segment
  POLYUNSIGNED targetAddress     // Offset in target segment
  uint32       targetSegment     // Segment index
  uint32       relKind           // ScanRelocationKind enum

[Segment data...]
[String table...]
[Dependency table...]
```

Module format is **semi-portable** with respect to object layout (segments are byte sequences), but relocations embed `ScanRelocationKind` codes that map directly to machine encodings (PROCESS_RELOC_I386RELATIVE, PROCESS_RELOC_ARM64ADRPLDR64, etc.; `scanaddrs.h:27–35`).

---

## 2. What Is "Portable" About `pexport.cpp`?

The term "portable" is misleading. It means:
- **Format portability**: The text format itself can be parsed on any OS/platform.
- **NOT architecture portability**: The format encodes the source architecture (X86 vs ARM, 32-bit vs 64-bit).

Evidence:
- Line 305–314 of `pexport.cpp`: Writes architecture marker and word size:
  ```cpp
  char arch = '?';
  switch (machineDependent->MachineArchitecture()) {
    case MA_X86_64: arch = 'X'; break;
    case MA_Arm64:  arch = 'A'; break;
  }
  fprintf(exportFile, "Root\t%" PRI_SIZET " %c %u\n", getIndex(rootFunction), arch, (unsigned)sizeof(PolyWord));
  ```
- Importer (line 549) calls `machineDependent->SetBootArchitecture(arch, wordLength)`, which may fail if source and target differ.
- All tagged integers, pointers, and code offsets are word-width-specific and endian-specific.

---

## 3. Native vs. Portable Export: When and How?

### Decision Point (`exporter.cpp`)
The `exportNative()` and `exportPortable()` C functions (lines 37–38 of `exporter.h`) are called from ML code. The user chooses which to call.

- **exportNative**: Emits ELF/Mach-O/COFF. Used for standalone executables. Produces object module relocations (e.g., R_X86_64_64).
- **exportPortable**: Emits text format. Used for interchange, debugging, or save states (via `PolyML.SaveState`).

### Loading Differences

**Native object file loading** (`mpoly.cpp`, startup):
1. OS loader executes the binary, placing code and data at fixed addresses.
2. Runtime finds `exportDescription` symbol in the binary (architecture-dependent lookup).
3. Memory table is extracted from the data segment.
4. All pointers are already absolute (relocations applied by linker/loader).

**Portable file loading** (`pexport.cpp:432–656`, `PImport::DoImport()`):
1. Text file is parsed line-by-line.
2. Objects are allocated in temporary space (`SpaceAlloc` class, lines 347–430).
3. Objects are created in two passes: first allocate all, then populate values.
4. Object references are stored as integer indices, then resolved to pointers.
5. Relocations within code (if present) are re-applied relative to new addresses.

### Entry Points

- Native: Direct function pointer from `exportDescription.rootFunction` (already at correct address).
- Portable: Index into object array, then pointer lookup in `objMap[]`.

---

## 4. Architecture Dependencies in the Heap

Every heap image is tightly bound to its source architecture. These must all be addressed in a portable format:

### 4.1 Word Size (32 vs. 64 bits)
- All `PolyWord` values are either 32 or 64 bits.
- Object lengths are stored as `POLYUNSIGNED` (word count).
- **Import handler**: `pexport.cpp:546` checks word size and calls `SetBootArchitecture()`, which may fail or recompile.
- **Problem for portability**: A 32-bit image cannot load on 64-bit without conversion. Tagged integers have different ranges (MAXTAGGED differs by word size; `globals.h:218`).

### 4.2 Endianness
- All multi-byte values (length words, tagged integers, code constants) are in native endian.
- No explicit byte-order marker in portable or module formats.
- **Problem**: A big-endian image will not load on little-endian.

### 4.3 Pointer Tagging Scheme
PolyML uses tag bits in `PolyWord`:
- Bit 0 set: Tagged integer (POLY_TAGSHIFT=1 on most platforms)
- Bit 0 clear: Object pointer
- High bit set (F_NEGATIVE_BIT): Used for encoding in some contexts

The tagging is consistent across all platforms but depends on word size. A 64-bit heap image will have 32 bits of integer payload after the tag; 32-bit has 16.

### 4.4 Object Pointer Encoding in 32-in-64 Mode
PolyML supports **32-in-64**: Run 32-bit ML code in a 64-bit process by using 32-bit pointers offset from `globalHeapBase` (a 64-bit base address). Example from `exporter.cpp:320–321`:
```cpp
if (space->isCode)
  newAddr = (PolyObject*)(globalCodeBase + (((uintptr_t)(obj->LengthWord()) & ~_OBJ_TOMBSTONE_BIT) * POLYML32IN64));
```
**In 32-in-64 mode**, the length word encodes not the actual byte size but an offset multiplier. The actual byte size is `offset * POLYML32IN64` (which is 2 or 4).

**Problem for portability**: A 32-in-64 image cannot be loaded as native 32-bit or 64-bit without re-encoding every pointer.

### 4.5 Native Machine Code
Code objects contain bytecode (on interpreted-only builds) or machine code (on native-code builds). Machine code is architecture-specific:
- x86-64: MOV, CALL, LEA instructions with RIP-relative addressing
- ARM64: ADRP, LDR, ADD instructions with page-relative addressing
- Cannot be moved without rewriting instruction constants

**Problem**: Machine code objects are not portable; the image must be regenerated.

### 4.6 Code Object Constant Area Offset
Code objects store:
- Machine code (first N bytes)
- Constant count (last 2 PolyWords, see `pexport.cpp:206`: `byteCount = (length - constCount - 2) * sizeof(PolyWord)`)
- Constants (final N PolyWords)

The offset from the code start to the constant area is stored as a relative byte offset, which depends on `sizeof(PolyWord)`.

### 4.7 Architecture-Specific Relocations
Within code, constants are relocated using machine-specific methods:
- **PROCESS_RELOC_DIRECT**: Direct 64-bit address (only on 64-bit)
- **PROCESS_RELOC_I386RELATIVE**: 32-bit RIP-relative (x86-64 only)
- **PROCESS_RELOC_ARM64ADRPLDR64**: ARM64 ADRP+LDR 64-bit pair
- **PROCESS_RELOC_ARM64ADRPLDR32**: ARM64 ADRP+LDR 32-bit pair
- **PROCESS_RELOC_ARM64ADRPADD**: ARM64 ADRP+ADD pair
- **PROCESS_RELOC_C32ADDR**: Compact 32-bit offset (32-in-64 only)

Each requires the target architecture's instruction set knowledge.

### 4.8 Summary of Architecture-Dependent Fields
```
Heap Image {
  POLYUNSIGNED word_size ✗
  bool endianness ✗
  PolyWord* globalHeapBase, globalCodeBase [32-in-64 only] ✗
  bool is_32_in_64_mode ✗
  MachineArchitecture (x86-64, ARM64, etc.) ✗
  
  [For each code object]
    byte[N] machine_code [or bytecode]
    POLYUNSIGNED code_offset_to_constants [depends on sizeof(PolyWord)]
    ScanRelocationKind[M] relocation_kinds [machine-specific]
    void*[M] relocation_targets [depend on base addresses]
}
```

---

## 5. Module System (`modules.cpp`)

PolyML's **module** system is **separate from but analogous to save state**:

### Module Structure
- **ModuleId**: 128-bit hash (2 × uint32_t) derived from module contents
- **Segments**: Named memory regions with flags (writable, executable, byte-only)
- **Relocations**: Explicit table of address fixups

### Key Difference from Heap Image
- Modules include a dependency table (line 141–142) listing required parent modules by name and ID
- Modules can be **layered**: A module loads on top of its parent and only stores differences
- Module IDs are computed as hashes of module contents (line 304 of `modules.cpp`: `copyScan.extractHash()`), allowing version checking

### Architecture Sensitivity
Modules are **architecture-specific**:
- Code objects contain native machine code.
- Relocations use `ScanRelocationKind` (architecture-dependent).
- Module dependency resolution uses both module ID and execution context (must run on same architecture).

**Relation to Save State**: Save states are implemented using the module system internally. A save state is a module with the executable as parent. Thus, save-state format shares all architecture dependencies.

---

## 6. Save State (`savestate.cpp`, `savestate.h`)

### Format
Save states use the **same module format** as `modules.cpp` (both use `StateExport` base class). The save-state file is a serialized snapshot of reachable objects from a given root with all dependencies marked.

### Call Stack
`PolyML.SaveState.saveState()` → `PolySaveState()` (exported C function) → `CopyScan::initialise()` → segments written via module exporter.

### Portability Characteristics
- **Not portable across architectures**: Inherits all architecture dependencies of the module format.
- **Portable across OS**: A save state made on Linux/x86-64 can load on a different Linux system (same architecture, same PolyML version).
- **Not forward-compatible**: PolyML version mismatches may cause rejections.

### Key Differences from Raw Heap Export
- Includes only reachable data from the root (not entire permanent spaces).
- Records module dependencies so parent modules can be unloaded if no longer needed.
- Can be layered: A child save state need not include data already in parent.

---

## 7. Hash/Sequence/Identity (`modules.cpp`, `exporter.cpp`)

### ModuleId Computation
Each module (and save state) is assigned a 128-bit ID computed from a rolling hash of its contents:
```cpp
// exporter.cpp:142–165
uint32_t hash_a = 0xdeadbeef, hash_b = 0xdeadbeef, hash_c = 0xdeadbeef;
hash_a += getBuildTime();         // Includes compile timestamp
hash_b += sequenceNo++;            // Per-export counter
// ...then hash_word is called for each reachable object
struct _moduleId extractHash();
```

### Use Cases
- **Version checking**: When loading a module, the stored ID is compared to expected ID. Mismatch indicates a version or rebuild issue.
- **Dependency verification**: Module headers include the parent module's ID, allowing verification before loading.
- **Uniqueness**: Different compilations of the same code get different IDs (due to `getBuildTime()` and sequence number), preventing accidental reuse.

### Non-Determinism
The hash includes timestamp (`getBuildTime()`) and sequence number, so identical code compiled at different times gets different IDs. This is intentional to avoid collisions across multiple sessions.

---

## 8. Options for Architecture-Portable Heap Images

Each option trades off between load-time speed, disk size, and implementation complexity. All must address the core problem: **executable code and pointer encodings are architecture-specific**.

### Option A: Store IR (Intermediate Representation) + Re-codegen at Load
**Approach**: Save the PolyML backend IR (or closer to source, e.g., `backendIC` from the compiler) and re-run code generation for the target architecture at load time.

**Pros:**
- Portable to any architecture with a backend.
- Handles all architectural variations automatically (word size, endianness, ABI).
- No need to pre-compile for each target.

**Cons:**
- Large on-disk size (IR is verbose; source-level IR even more so).
- **Very slow load time**: Full code generation happens at startup (seconds to minutes for a large heap).
- Requires shipping a compiler (or JIT) with the runtime.
- Risk of version skew: IR format may change, breaking old files.

**Complexity**: High. Requires serializing and deserializing the entire compilation pipeline.

### Option B: Store Bytecode + JIT Lazily at Load
**Approach**: Compile to a portable bytecode (e.g., stack-machine IR, WAM, or a custom format) and JIT each function on first call.

**Pros:**
- Portable across architectures.
- Lazy load: Functions only JIT'ed when used; startup is fast.
- Modest disk size (bytecode is denser than source IR).
- Can cache JIT'd code across sessions (if needed).

**Cons:**
- Adds latency to first call of each function.
- Requires a JIT compiler in the runtime (adds complexity and binary size).
- Bytecode format itself may not be fully portable (depend on assumptions about pointers, word size).
- Non-deterministic performance: First call to hot code is slow.

**Complexity**: Medium-high. Requires a separate bytecode format and JIT infrastructure.

### Option C: Store Cranelift IR (CLIF) + Let Cranelift Target Load-Time Arch
**Approach**: Use Cranelift (or similar compiler library like LLVM bitcode) as the intermediate representation and let it emit code for the target during load.

**Pros:**
- True architecture portability: Cranelift targets multiple architectures.
- Better code quality than custom bytecode (sophisticated optimization passes).
- Well-engineered, battle-tested infrastructure.
- Separates PolyML's IR from backend concerns.

**Cons:**
- Large binary footprint (Cranelift is ~2MB compiled).
- Load-time code generation is slower than pre-compiled code (seconds for large heaps).
- Adds external dependency (Cranelift/LLVM).
- Still requires re-serialization of PolyML's internal representation to Cranelift IR.

**Complexity**: High. Requires integration with a mature compiler framework.

### Option D: Store Abstract Object Representation + Recompute Pointers at Load
**Approach**: Serialize objects as abstract entities (types, sizes, fields) with placeholder pointers. At load time, reconstruct the object graph, recompute addresses, and fix all relocations.

**Pros:**
- No code re-generation needed; non-executable data (values, closures) remains unchanged.
- Supports machine code by storing it separately and re-linking at load.
- Moderate disk size (one copy of data per object).
- Load time is O(number of objects) + relocation cost.

**Cons:**
- Still requires machine code to be stored by architecture (or regenerated).
- Requires a sophisticated loader with knowledge of all pointer encodings and relocation types.
- Complex to support all PolyML's object types (closures, code, strings, arbitrary-precision numbers, etc.).
- If code is stored natively, no gain over status quo.
- If code is regenerated, regresses to Option A/B/C.

**Complexity**: Medium. Doable but requires careful design of the abstract representation and loader.

### Recommendation

**Option B + D Hybrid**:
1. **Store bytecode for code objects**; compile to native code at load time or on-demand JIT.
2. **Store abstract objects for non-code data**; re-materialize at load time with pointer fixups.
3. **Use a custom, simple bytecode** (not CLIF, not WAM—PolyML-specific) optimized for PolyML's execution model (unboxed args, closure calling convention).

This avoids the complexity of a full compiler library and the re-generation overhead of IR-based approaches, while enabling portability. The bytecode interpreter can be fast enough for startup, and JIT can be added later.

---

## References

- `libpolyml/exporter.h`: Lines 1–92 (Exporter base class)
- `libpolyml/exporter.cpp`: Lines 136–245 (CopyScan initialization and object copying)
- `libpolyml/pexport.h`: Lines 37–62 (PExport class)
- `libpolyml/pexport.cpp`: Lines 62–339 (Portable export writer) and 432–656 (Portable import reader)
- `libpolyml/memmgr.h`: Lines 39–175 (Memory space types and ModuleId)
- `libpolyml/scanaddrs.h`: Lines 26–36 (Relocation kinds)
- `libpolyml/modules.cpp`: Lines 119–188 (Module file format structures)
- `libpolyml/modules.cpp`: Lines 207–245 (Module exporter and relocation writing)
- `libpolyml/savestate.cpp`: Lines 121–128 (Save state entry points)
- `libpolyml/savestate.h`: Lines 26–37 (Save state / module export shared interface)
- `polyexports.h`: Lines 47–76 (C ABI structures for exportDescription and moduleId)
- `libpolyml/globals.h`: Lines 139–221 (PolyWord tagging and pointer encodings)

