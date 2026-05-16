# PolyML Garbage Collector: Deep Survey

## Executive Summary

PolyML uses a **two-phase generational GC system**: a fast copying minor GC (QuickGC) moving allocation-space data into permanent regions, and a three-phase major GC (mark-copy-update) that compacts heaps in place using forwarding pointers encoded in object length words. The system is **parallel at phase boundaries** (mark, copy, update tasks distributed to worker threads), **stop-the-world per phase**, uses **precise stack scanning** (architecture-specific frame walking), and employs **no explicit write barrier**—mutability tracking is implicit in the object type system. The 32-in-64 variant compresses pointers to 32-bit indices off `globalHeapBase`, requiring careful layout in the mark and copy logic.

---

## 1. GC Algorithm Shape

**Algorithm type**: Generational, mark-and-compact, parallel-phase-based.

### High-level phases:

1. **Minor GC (QuickGC)**: copying collector. All objects in allocation areas are copied into mutable/immutable permanent areas. Fails if target areas overflow.  
   - **File**: `quick_gc.cpp:20-24` — "Quick copying garbage collector that moves all the data out of the allocation areas"
   - **Entry**: `QuickGC()` in `gc.h:35`

2. **Major GC (Full GC)**: three-phase compacting collector:
   - **Mark Phase**: roots→reachable objects; sets `_OBJ_GC_MARK` bit in length word; parallel stack-stealing among GC threads.
   - **Copy Phase** (Compaction): moves marked objects; writes forwarding pointers (tombstones) in old locations.
   - **Update Phase**: follows forwarding chains to fix internal pointers.

**File** `gc.cpp:69-101` describes the major GC:
> "1. Mark phase... 2. Compact phase... 3. Update phase... The GC has a sharing phase... performed before the mark phase."

### Entry points:

- **Full GC**: `FullGC(TaskData*)` in `gc.cpp:387`; requested via `FullGCRequest` for signal-safe queueing.
- **Minor GC**: `RunQuickGC(POLYUNSIGNED wordsRequired)` in `quick_gc.cpp`; called first in `doGC()` at line 376.
- **Major GC orchestration**: `doGC()` in `gc.cpp:102-333`.

### Barrier between phases:

- After **Mark**: `gpTaskFarm->WaitForCompletion()` in `gc_mark_phase.cpp:842`.
- After **Copy**: phase rescan; before **Update**: also barriers via `gpTaskFarm->WaitForCompletion()`.
- Coordination via **GCTaskFarm**: work queue with semaphore + lock (file `gctaskfarm.h:45-91`).

---

## 2. Heap Regions & Spaces

**Space types** (enum `SpaceType` in `memmgr.h:39-46`):

```c
ST_PERMANENT,  // Linked to executable; immutable or saved state
ST_LOCAL,      // Volatile, garbage-collected (mutable or immutable)
ST_EXPORT,     // Temporary export area
ST_STACK,      // ML stack per thread
ST_CODE        // JIT-compiled code (mutable during construction, read-only later)
```

### Space tracking (MemMgr in `memmgr.h:269-487`):

- **pSpaces**: permanent spaces (fixed, used as GC roots)
- **lSpaces**: local heaps (collected); stored in order: immutable → mutable → allocation
  - Each local has `isMutable` flag and bitmap (`memmgr.h:216`)
- **cSpaces**: code spaces (collected, but rarely); each has `headerMap` for code reloc
- **sSpaces**: thread stacks (not collected, but scanned)

### Allocation layout within LocalMemSpace:

- `bottom` → `lowerAllocPtr`: newly allocated objects (minor GC scans upward)
- `upperAllocPtr` → `top`: free space

**Minor GC invariant**: allocation areas are young; data copied to persistent mutable/immutable areas.  
**Major GC invariant**: immutable and mutable areas are separate; data compacted top-down within each.

### Address resolution (hot path):

`SpaceForAddress()` in `memmgr.h:341-356` uses a B-tree to map address→space in O(8 * bits/8) = O(1) in practice.

---

## 3. GC Roots

### Root sources:

1. **Permanent mutable areas** (`gc_mark_phase.cpp:604-608`):
   ```cpp
   for (auto space : gMem.pSpaces)
       if (space->isMutable && !space->byteOnly)
           marker->ScanAddressesInRegion(space->bottom, space->top);
   ```

2. **RTS modules** (`gc_mark_phase.cpp:612`):
   ```cpp
   GCModules(marker);  // Scans RTS registrations (streams, refs, thread-locals, etc.)
   ```

3. **Thread stacks** (architecture-specific, per-thread):
   - x86/ARM64 register saved state + stack frame walk
   - **File** `interpreter.cpp:182` (bytecode), `x86_dep.cpp:200` (x86), `arm64.cpp:138` (ARM64)
   - Example: `Arm64TaskData::ScanStackAddress()` walks ML stack frames, yielding data pointers and code return addresses.

### Precision:

**Precise stack scanning**: each architecture walks saved registers and stack frames, filtering tagged integers. No conservative scanning over C stack.

---

## 4. Stack Scanning & Safepoints

### Mechanism:

**No inline safepoint checks**. Instead:

1. **Stop-the-world at GC initiation**:  
   - Main thread requests GC via `FullGCRequest` or `QuickGCRequest` (queued to avoid signal-safety issues)
   - Compiled ML code polls for requests at **function entry/exit** and **backward branches**
   - Threads pause when they detect pending GC request

2. **Precise frame reconstruction**:
   - When thread is suspended, saved CPU context (via `GetThreadContext()` or signal handlers) gives register state
   - Runtime walks stack frames backward (via return addresses) to enumerate all ML values
   - No stack maps; instead, uses **type metadata in length words** to determine which words are pointers

**File** `gc_mark_phase.cpp:611-612` + per-thread context shows this model:
> "Scan the RTS roots... GCModules(marker)" then thread stacks are scanned in parallel

### Implementation note:

Architecture-dependent. Example for ARM64 (`arm64.cpp:353-360`):
```cpp
for (auto q : stack) {
    ScanStackAddress(process, *q, stack);  // Walk each word
}
for (unsigned i = 0; i < NUM_REGISTERS; i++) {
    ScanStackAddress(process, assemblyInterface.registers[i], stack);
}
```

---

## 5. Write Barrier

**None**. The system relies on:

1. **Object type bits** (`globals.h:247`):
   - `F_MUTABLE_BIT` (0x40): set if object is mutable
   - **Invariant**: only mutable objects in local heap can point to local objects
   - **Consequence**: if looking for references from permanent→local, only scan permanent mutables

2. **Type-based filtering** in `gc_mark_phase.cpp:432-436`:
   ```cpp
   if (OBJ_IS_WEAKREF_OBJECT(lengthWord)) { /* special case */ }
   else if (OBJ_IS_CODE_OBJECT(lengthWord)) { /* scan code relocations */ }
   else if (OBJ_IS_CLOSURE_OBJECT(lengthWord)) { /* first word is code */ }
   // else: normal word object → scan all words
   ```

3. **No card marking, no remembered set**.  
   **Why it works**: Minor GC copies all allocation-space data immediately; major GC marks all reachable data; mutable permanents are roots.

---

## 6. Allocation Fast Path

### QuickGC allocation (minor GC):

From `quick_gc.cpp:228-249`, the root scanner allocates into the first fitting space:
```cpp
LocalMemSpace *RootScanner::FindSpace(POLYUNSIGNED n, bool isMutable) {
    LocalMemSpace *lSpace = isMutable ? mutableSpace : immutableSpace;
    if (lSpace && lSpace->freeSpace() > n) return lSpace;
    // else find largest free space
    for (auto sp : gMem.lSpaces) {
        if (sp->isMutable == isMutable && !sp->allocationSpace &&
            (!lSpace || sp->freeSpace() > lSpace->freeSpace()))
            lSpace = sp;
    }
    return lSpace;
}
```

**Inline codegen path** (not visible in C++, but referenced):
- Compiled code allocates via **bump pointer in allocation space**
- Length word + data written, allocation pointer decremented
- QuickGC scans upward from `partialGCScan` to `upperAllocPtr`

### Major GC allocation (copy phase):

From `gc_copy_phase.cpp:93-94`, per-thread ownership:
```cpp
static inline PolyWord *FindFreeAndAllocate(
    LocalMemSpace *dst, uintptr_t limit, uintptr_t n) {
    // Search downward in dst's bitmap for n free words
    // Mark bits set in bitmap
}
```

**Thread-safe**: once a thread "takes ownership" of a space (copy phase), it alone copies into that space (lock at `gc_copy_phase.cpp:87`).

### 32-in-64 special case:

In `quick_gc.cpp:216-219`, after copying alignment padding:
```cpp
#ifdef POLYML32IN64
while (lSpace->lowerAllocPtr < lSpace->upperAllocPtr && 
       ((lSpace->lowerAllocPtr - 0) & (POLYML32IN64 - 1)) != POLYML32IN64 - 1)
    *lSpace->lowerAllocPtr++ = PolyWord::FromUnsigned(0);
#endif
```
Ensures pointers are correctly aligned for 32-bit index encoding.

---

## 7. Concurrency & GCTaskFarm

**File** `gctaskfarm.h:45-91` and `gctaskfarm.cpp`.

### Structure:

```cpp
class GCTaskFarm {
    PSemaphore waitForWork;    // Signals workers when work available
    PLock workLock;            // Protects queue
    PCondVar waitForCompletion; // Main thread waits here
    unsigned threadCount;       // Number of worker threads
    unsigned activeThreadCount; // Workers currently executing
};
```

### Work model:

- **Mark phase**: `MTGCProcessMarkPointers::MarkPointersTask()` (`gc_mark_phase.cpp:255`)
  - Worker threads steal unprocessed objects from shared mark stacks
  - Each thread has local `markStack[MARK_STACK_SIZE]` (3000 entries, `gc_mark_phase.cpp:83`)
  - Idle threads pull from other threads' stacks (work stealing)

- **Copy phase**: `GCCopyPhase()` spawns region-copy tasks
  - Each thread claims ownership of a source/dest pair, avoiding locks in inner loop

- **Update phase**: similar; each task updates one region

### Synchronization:

- `gpTaskFarm->WaitForCompletion()`: main thread blocks on `waitForCompletion` condition variable
- Condition signaled when all queued items processed + no worker active
- **No fine-grained locking in mark/copy inner loops**: only phase-level barriers

---

## 8. Tricky Bits

### Weak References:

**File** `gc_check_weak_ref.cpp:49-100`.

- Objects flagged `F_WEAK_BIT` (0x20, `globals.h:244`) contain optional references
- Cell structure: `[SOME(ref) | SOME(ref) | ...]`
- After mark phase, check each SOME value against bitmap
- If not marked → set to NONE (0), notify via `convertedWeak` flag

### Forwarding Pointers (Tombstones):

- **Length word encoding** (`globals.h:292-299`):
  ```cpp
  inline bool OBJ_IS_POINTER(POLYUNSIGNED L) { return (L & _OBJ_TOMBSTONE_BIT) != 0; }
  inline PolyObject* OBJ_GET_POINTER(POLYUNSIGNED L) {
      return (PolyObject*)(globalHeapBase + (((uintptr_t)L & ~_OBJ_TOMBSTONE_BIT) * POLYML32IN64));
  }
  ```
- Copy phase overwrites old length word: `obj->SetForwardingPtr(newAddress)`
- Update phase follows chain: `while (obj->ContainsForwardingPtr()) obj = obj->GetForwardingPtr();`
- **32-in-64**: pointer stored as index (bits shifted by `POLYML32IN64` steps)

### Mark Stack Overflow:

**File** `gc_mark_phase.cpp:138-223`.

- If mark stack fills, record range (`fullGCRescanStart`, `fullGCRescanEnd`) in space lock
- After root marking complete, rescan any ranges with overflowed stacks
- Repeat until no new overflows (usually converges quickly)

### Large Object Cache:

**File** `gc_mark_phase.cpp:150-155`.

- For objects > 50 words, cache current scan position to avoid rescanning
- Ring buffer `largeObjectCache[LARGECACHE_SIZE]` stores `{base, current_ptr}`

### Code Object Special Handling:

- **Type bits** distinguish code from data
- Code objects scanned via `ScanAddress::ScanAddressesInObject()` which processes relocations (`scanaddrs.h:80`)
- Closure objects (`F_CLOSURE_OBJ`, 0x03) have first word as **absolute code address** (32-in-64 only), rest is normal tuple

### Sharing Phase (Data Deduplication):

**File** `gc_share_phase.cpp` (not detailed in survey, but referenced at `gc.cpp:120-124`).

- Optional expensive pass before mark
- Merges identical immutable objects
- Enabled heuristically based on prior savings

### 32-in-64 Pointer Compression:

**File** `globals.h:71-79, 125-135, 162-173`.

- `POLYML32IN64` = 2 or 4 (default 2): granule size for index encoding
- All pointers stored as `(address - globalHeapBase) / (POLYML32IN64/2)` in 32 bits
- **Consequence for GC**: forwarding pointers, bitmap addressing all scaled by this factor
- Example in mark phase: `markStack` entries are absolute pointers; when encoding forwarding: scale down

---

## Consequences for Rust Rewrite

### 1. **Stack Scanning** (Critical):
   - Cannot use conservative scanning; must preserve architecture-specific frame walk
   - Rust unwinding may differ from C++ exception handling; safepoint polling model must adapt
   - Saved CPU context → PolyWord enumeration requires careful lifetime management

### 2. **Cranelift Integration** (Critical):
   - Cranelift-generated code must emit safepoint polls at function entry and loop back-edges
   - Return address handling differs; ensure frame layout matches scanner expectations
   - For ARM64/x86: register allocation must respect ML value register conventions (if any)

### 3. **Forwarding Pointers**:
   - Length word encoding is implicit; Rust must preserve the exact layout
   - Consider using a dedicated `enum ForwardingOrLength` type for safety
   - In 32-in-64: index arithmetic must exactly match C++ logic

### 4. **No Write Barrier**:
   - Simplifies initial implementation but requires strong invariant checking
   - Mutable-immutable separation is **essential**; violations = memory corruption
   - Consider tagging allocations at creation time to catch violations early

### 5. **Parallel Mark/Copy/Update**:
   - Work-stealing mark stacks are **not trivial** to parallelize without bugs
   - Overflow detection + rescan loop requires careful synchronization
   - Recommend starting single-threaded, then add gctaskfarm equivalent incrementally

### 6. **Heap Metadata**:
   - Bitmap allocation and fast `SpaceForAddress()` tree are performance-critical
   - Rust Vec-based space lists are fine, but B-tree or similar for address lookup required
   - 32-in-64 index scaling affects bitmap and address calculations throughout

---

## Code File Index

| Aspect | File(s) |
|--------|---------|
| **GC orchestration** | `gc.cpp`, `gc.h` |
| **Minor GC** | `quick_gc.cpp` |
| **Mark phase** | `gc_mark_phase.cpp` |
| **Copy phase** | `gc_copy_phase.cpp` |
| **Update phase** | `gc_update_phase.cpp` |
| **Weak ref check** | `gc_check_weak_ref.cpp` |
| **Sharing phase** | `gc_share_phase.cpp` |
| **Parallel dispatch** | `gctaskfarm.h`, `gctaskfarm.cpp` |
| **Space & bitmap mgmt** | `memmgr.h`, `memmgr.cpp` |
| **Bitmap ops** | `bitmap.h`, `bitmap.cpp` |
| **Stack scanning** | `interpreter.cpp`, `x86_dep.cpp`, `arm64.cpp` (arch-specific) |
| **Object model** | `globals.h` |
| **Root scanner** | `scanaddrs.h`, plus overrides in phase files |
| **Heap sizing** | `heapsizing.h`, `heapsizing.cpp` |

---

## Unknowns & Caveats

1. **Finalization**: not surveyed; check for finalizer queues in RTS modules
2. **Profiling hooks**: code object profiling bitmaps touched but not detailed
3. **Sharing phase cost model**: heuristic for when to run; see `heapsizing.h:78-80`
4. **Paging detection**: references at `gc.cpp:209-232` suggest some VM-aware tuning
5. **StrongARM/SPARC**: only x86, ARM64, and generic C++ implementations are visible; older ports may exist elsewhere
