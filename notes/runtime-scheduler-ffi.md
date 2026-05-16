# PolyML Runtime Architecture: Scheduler, Threading, FFI, and Exception Handling

## Executive Summary

PolyML uses a **1:1 threading model** where each ML thread maps to an OS thread (pthread on Unix, Windows threads on Windows). The GC is stop-the-world with a global `schedLock` that all threads must acquire during scheduling decisions. Compiled code calls into the RTS via explicit `POLYEXTERNALSYMBOL` functions, passing the thread ID explicitly. Exception handling uses an on-stack handler chain (via `handlerRegister`) that points into the ML stack itself, with exceptions raised via C++ exceptions in the RTS that translate to SML exception packets. FFI uses direct `dlopen`/`LoadLibrary` calls; callback support is minimal (via `PolyFFICallbackException` trap).

---

## 1. Threading Model: 1:1 OS Mapping

**Source**: `libpolyml/processes.h:105-196`, `libpolyml/processes.cpp:327-950`

PolyML implements **1:1 threading**: each ML thread (`PolyObject` of type `ThreadObject`) is backed by exactly one OS thread. The ML value space does not use green threads, fibers, or M:N scheduling.

### Thread Lifecycle

- **Creation**: `PolyThreadForkThread()` (RTS entry, `processes.cpp:347`) creates a new `pthread_t` (Unix) or `HANDLE` (Windows) and wraps it in a C++ `TaskData` object.
- **Identification**: Each thread has a `ThreadObject` heap object (accessed via `threadRef` weak reference from `TaskData`; see `FindTaskForId()` at `processes.h:155-157`). The thread ID is passed explicitly to all RTS functions.
- **Termination**: `ThreadExit()` (`processes.h:198`) tears down the `TaskData`, notifies the scheduler, and exits the OS thread.

### GC Coordination

GC is **stop-the-world, single-threaded**:

1. When heap exhaustion occurs (e.g., in `FindAllocationSpace`, `processes.cpp:947`), a thread calls `QuickGC()` or requests a full GC via `MakeRootRequest()`.
2. The thread making the GC request sets `inMLHeap = false` (line 175), signaling that it has released exclusive claim on the ML memory.
3. Other threads must acquire `schedLock` (line 287) before modifying `threadRequest` or accessing `taskArray` (line 280).
4. All threads call `ThreadUseMLMemory()` / `ThreadReleaseMLMemory()` to coordinate: only one thread may be in ML memory at a time while GC is active.
5. The root thread (initial thread) drives the actual GC logic; worker threads block on `mlThreadWait` (line 307) until GC completes.

**Consequence for Cranelift/Rust rewrite**: You cannot use Rust async/await or green threads—you need 1:1 thread binding. Each ML thread must own its own Rust `std::thread` or tokio task. Signal handlers must use thread-local state (Unix only; Windows has no signal support).

---

## 2. TaskData: Per-Thread State and Access Pattern

**Source**: `libpolyml/processes.h:105-196`, `libpolyml/arm64.cpp:102-179`, `libpolyml/interpreter.cpp:60-97`

### Core Fields

The `TaskData` class (subclassed as `Arm64TaskData` and `IntTaskData` for native and bytecode execution) holds:

```cpp
class TaskData {
    PolyWord *allocPointer;     // Allocation pointer (decremented towards limit)
    PolyWord *allocLimit;       // Lower bound of current heap segment
    uintptr_t allocSize;        // Preferred heap segment size (words)
    StackSpace *stack;          // ML evaluation stack
    ThreadObject *threadObject; // Heap reference to ML thread object
    SaveVec saveVec;            // GC-safe roots during RTS call
    int lastError;              // errno from last FFI call
    void *signalStack;          // Signal delivery stack (Unix)
    PCondVar threadLock;        // For blocking on mutexes/CV
    ThreadRequests requests;    // Interrupt/kill flags
    PolyObject *blockMutex;     // Mutex being waited on
    bool inMLHeap;              // True if thread is in ML code (prevents GC)
};
```

For **native ARM64 code**, `Arm64TaskData` adds:

```cpp
typedef struct _AssemblyArgs {
    stackItem *handlerRegister;     // Exception handler chain head
    stackItem *stackLimit;          // Stack overflow check point
    stackItem exceptionPacket;      // Current exception (if any)
    stackItem threadId;             // Copy of thread ID (in X26 at runtime)
    stackItem registers[25];        // Save area for X0-X24
    double fpRegisters[8];          // FP reg save area D0-D7
    PolyWord *localMbottom;         // Heap base + 1
    PolyWord *localMpointer;        // Allocation pointer (X27)
    stackItem *stackPtr;            // Stack pointer (X28)
    arm64CodePointer linkRegister;  // Return address (X30)
    arm64CodePointer entryPoint;    // Current PC
    byte returnReason;              // Why we exited to C++
} AssemblyArgs;
```

### Access Pattern: Register-Based

**Native code (ARM64)**:
- **X26** always holds a pointer to the per-thread `AssemblyArgs` struct (set in `EnterPolyCode()`, arm64.cpp:690).
- Heap pointers and stack pointer are held in **X27** (allocation pointer) and **X28** (stack pointer) during ML execution.
- All RTS calls must first retrieve the thread ID from a register or stack, then call `TaskData::FindTaskForId()` (line 156) to recover the C++ object.

**Bytecode interpreter**:
- `IntTaskData` subclass stores `stackItem *taskSp` and `stackItem *hr` (handler register) as C++ members.
- Access is direct pointer dereference, not register-based.

**Critical detail**: `FindTaskForId()` performs a two-level dereference:
```cpp
static TaskData *FindTaskForId(PolyWord taskId) {
    return *(TaskData**)(((ThreadObject*)taskId.AsObjPtr())->threadRef.AsObjPtr());
}
```
This means the thread ID (a heap object) contains a weak reference to the `TaskData`; during GC, this reference may move but is updated by `GarbageCollect()` (arm64.cpp:335-346).

---

## 3. RTS Call ABI and Conventions

**Source**: `libpolyml/rtsentry.h`, `libpolyml/basicio.cpp:1080-1103`, `libpolyml/arm64.cpp:161-165`, `libpolyml/processes.cpp:347-365`

### Entry Point Signature

All RTS functions follow this pattern:

```cpp
typedef void (*polyRTSFunction)();  // Untyped function pointer

POLYUNSIGNED PolyFunctionName(POLYUNSIGNED threadId, POLYUNSIGNED arg1, POLYUNSIGNED arg2, ...)
{
    TaskData *taskData = TaskData::FindTaskForId(threadId);
    taskData->PreRTSCall();         // Save heap pointers, drop ML-memory lock if needed
    Handle reset = taskData->saveVec.mark();
    
    try {
        // Do work, allocate via taskData->saveVec.push()
        result = ...;
    }
    catch (KillException &) {
        processes->ThreadExit(taskData);
    }
    catch (...) { }                 // Suppress ML exceptions that weren't caught
    
    taskData->saveVec.reset(reset);
    taskData->PostRTSCall();        // Restore heap pointers
    
    return result ? result->Word().AsUnsigned() : TAGGED(0).AsUnsigned();
}
```

### Calling Convention (ARM64 Native)

1. **Thread ID**: Passed as first argument in **X0** (ARM64 calling convention ABI).
2. **Other arguments**: X1, X2, X3, etc. (standard AAPCS).
3. **Return value**: X0 (tagged word).
4. **Allocation and memory state**: Saved/restored in `PreRTSCall()`/`PostRTSCall()` via `SaveMemRegisters()` and `SetMemRegisters()` (arm64.cpp:169-170).

### The SaveVec Mechanism

`SaveVec` (member of `TaskData`) is a handle-based root set during RTS execution:
- `saveVec.mark()` saves a checkpoint.
- `saveVec.push(word)` returns a `Handle` (guaranteed-to-be-live GC root) for objects allocated during the RTS call.
- `saveVec.reset(checkpoint)` pops back to the checkpoint, discarding temporary roots.
- This allows the GC to traverse live ML objects held by RTS functions without tracing C++ stack frames.

### Exception Propagation

If an RTS function raises a C++ exception (e.g., `raise_exception0(taskData, EXC_divide)` in arb.cpp), the function catches it, discards the result, and returns `TAGGED(0)`. The exception packet is stored in `TaskData` (or `Arm64TaskData::assemblyInterface.exceptionPacket`) and checked by the ML interpreter on return.

---

## 4. Allocation Overflow and GC Entry

**Source**: `libpolyml/processes.cpp:947-1046`, `libpolyml/arm64.cpp` (assembly glue)

### Local Allocation Buffer

Each thread has a thread-local allocation buffer (`allocPointer` and `allocLimit`). Compiled code decrements `allocPointer` by the object size. If `allocPointer < allocLimit + words`, heap exhaustion is signaled.

### GC Trigger Mechanisms

1. **Implicit check in generated code**: Arm64 native code includes a bounds check at function entry:
   - Compare `allocPointer - words` against `allocLimit`.
   - If exhausted, call `heapOverFlowCall` (a trampoline to RTS, set at arm64.cpp:108).

2. **Explicit RTS call**: Compiled code can directly invoke `FindAllocationSpace()` (processes.cpp:947) if space is needed without allocation:
   - First checks if the current segment has space.
   - If not, tries to allocate a new segment from `gMem.AllocHeapSpace()`.
   - If that fails, runs `QuickGC()` (defined in gc module, not shown here).
   - If GC fails, interrupts all threads via `BroadcastInterrupt()` and pauses for 5 seconds before retrying.

3. **Root thread coordination**: When a non-root thread needs GC, it calls `MakeRootRequest()` (processes.cpp:223) to ask the root thread to perform full GC while worker threads wait on `mlThreadWait`.

### Consequence for Cranelift

Cranelift will need to:
1. Generate ARM64 code that respects the allocation pointer / limit convention (X27 or similar register).
2. Emit bounds checks at function prologue and before large allocations.
3. Call a fixed `heapOverFlowCall` entry point (a trampoline) that marshals to the RTS.
4. Not use Rust's standard allocator; instead, use the PolyML heap as the only allocation source.

---

## 5. Signal Handling: Stack Overflow, SIGSEGV, SIGFPE

**Source**: `libpolyml/sighandler.h`, `libpolyml/sighandler.cpp:78-147`, `libpolyml/arm64.cpp:670-830`

### Unix Signal Setup

PolyML uses POSIX signals for:
- **Profiling** (SIGPROF): Timer-driven interrupts to sample the current PC.
- **User-installed handlers** (any signal): ML code can register a handler via `PolySetSignalHandler()`.
- **Asynchronous interrupts**: Signals wake up blocked threads.

### Mechanism

1. **Per-thread signal stack** (Unix only, `TaskData::signalStack`):
   - Allocated via `initThreadSignals()` (sighandler.cpp:44).
   - Installed via `sigaltstack()` to provide a safe signal delivery context.

2. **Signal detection thread**:
   - A dedicated ML thread blocks on `WaitForSignal()` (processes.h:341), waiting for signals.
   - When a signal arrives, `sigLock` is acquired, `sigData[sig].signalCount` is incremented (sighandler.cpp:141-143).
   - The detection thread is woken and dispatches to ML handlers.

3. **Non-maskable signals** (for RTS use):
   - `SIGSEGV`, `SIGFPE` (if used for null checks or traps): The signal handler examines the faulting address and instruction. If it's a known trap (e.g., a null-dereference or allocation trap), the signal is converted to an exception; otherwise, the program terminates.
   - Currently, PolyML **does not use signals for allocation or null-pointer traps**; those are handled via explicit code checks.

### Stack Overflow Detection

- Not via signal; instead, explicit checks in prologue against `stackLimit` (AssemblyArgs.stackLimit, arm64.cpp:113).
- If a function requires more space than available, it calls `stackOverFlowCall` (arm64.cpp:109), which raises an exception in the RTS.

### Consequence for Rust Rewrite

- Rust's panic unwinding will interfere with signal handlers unless you carefully use `catch_unwind()` and manual cleanup.
- You cannot rely on Rust's standard panic mechanism; instead, implement C++-style exception translation.
- TLS (via `pthread_key_t` on Unix, `TlsGetValue` on Windows) is used to retrieve `TaskData` from a signal handler; Rust's thread-local variables should work identically.

---

## 6. Exception Model: Stack-Based Handler Chain

**Source**: `libpolyml/arm64.cpp:102-180`, `libpolyml/interpreter.cpp:60-97`, `libpolyml/bytecode.cpp` (exception handling opcodes)

### On-Stack Handler Chain

ML exceptions do **not** use tables or unwinding metadata. Instead:

1. **Handler pointer** is kept in `handlerRegister` (part of `AssemblyArgs` or interpreter state).
2. When ML code enters an exception handler (via `handle` expression), it pushes a frame onto the ML stack and updates `handlerRegister` to point to that frame.
3. When an exception is raised:
   - The `exceptionPacket` (a PolyWord containing an ML exception object) is stored in `TaskData`.
   - The interpreter / native code jumps to the exception handler by loading `handlerRegister` as the stack pointer and resuming.
   - No unwinding of C++ frames occurs; the exception is purely in the ML value space.

### Exception Raising (From RTS)

C++ code in the RTS uses C++ exceptions internally:

```cpp
raise_exception0(taskData, EXC_divide);  // Defined as raiseException0WithLocation in run_time.h
```

These are caught at the RTS boundary (basicio.cpp:1097: `catch (...) { }`), and the exception packet is set:

```cpp
taskData->SetException(exception_object);  // Sets assemblyInterface.exceptionPacket
```

On return to ML, the exception is checked; if non-null, the interpreter raises it in the ML context (bytecode.cpp: exception handling opcodes).

### Bytecode vs. Native

- **Bytecode**: Uses interpreter-local `exception_arg` and `hr` (handler register) fields (interpreter.cpp:75, 94).
- **Native**: Uses `AssemblyArgs::exceptionPacket` and `AssemblyArgs::handlerRegister` (arm64.cpp:114, 112).

Both are scanned by GC during `GarbageCollect()` to ensure exception packets are not dangling pointers.

### Consequence for Cranelift

- You need an on-stack exception handler chain: a linked list (or array) of exception frames on the ML stack.
- No zero-cost exception tables or DWARF unwinding.
- Each `handle` expression must allocate a frame on entry and restore the previous handler on exit.
- Exceptions raised from the RTS must update a `current_exception` field in the per-thread state, and the interpreter must check it on return.

---

## 7. Foreign Function Interface (FFI)

**Source**: `libpolyml/polyffi.cpp:75-185`, `libpolyml/polyffi.cpp:109-141`, `libpolyml/processes.cpp` (thread coordination)

### Dynamic Library Loading

PolyML uses standard OS APIs:
- **Unix**: `dlopen()` (line 167), `dlsym()` (not shown; used via `PolyFFIGetSymbolAddress`).
- **Windows**: `LoadLibrary()` (line 154), `GetProcAddress()`.

No libffi or code generation is visible in the surveyed code. Instead:

1. ML code calls `PolyFFILoadLibrary()` (an RTS function) to load a `.so` or `.dll`.
2. ML code obtains a function pointer via `PolyFFIGetSymbolAddress()`.
3. ML code invokes the function pointer directly (compiled code must generate the call instruction and marshal arguments).

### Callback Support

**Minimal and implicit**:
- When C code calls back into ML, it must have obtained an ML function pointer.
- If a callback raises an ML exception, `PolyFFICallbackException()` (polyffi.cpp:418) is invoked by the C wrapper (likely generated by the compiler or hand-written).
- The exception message is logged, and control is returned to C with an error code.

**No automatic callback wrappers**: Unlike libffi, PolyML does not generate closures or trampolines for callbacks. The compiler must emit code to call a wrapper function.

### FFI and GC

**Critical invariant**: When a thread enters foreign code:

1. `TaskData::inMLHeap = false` (processes.cpp:173-175).
2. `ThreadReleaseMLMemory()` is called (processes.h:316) to signal that this thread is not holding exclusive access to ML memory.
3. GC can proceed while the thread is in C code.
4. On return, `ThreadUseMLMemory()` reacquires the lock (if needed).

This is coordinated via `PreRTSCall()` / `PostRTSCall()`:
- `PreRTSCall()` drops `inMLHeap` and may wait for GC to complete.
- `PostRTSCall()` resets the allocation pointers and allows GC to resume.

### Consequence for Cranelift

- FFI calls must explicitly release the ML-memory lock before entering C code.
- The GC must be aware of which threads are in C code (marked by `inMLHeap = false`).
- No JIT generation of callbacks; callbacks must be statically defined or use a generic wrapper.

---

## 8. Bytecode Interpreter Existence and Role

**Source**: `libpolyml/interpreter.cpp:1-97`, `libpolyml/bytecode.cpp:1-90`

### When Used

Bytecode is used **only during bootstrap** (initial startup):

1. At program startup, the compiler-generated code is in bytecode form (stored in the heap image).
2. The bytecode interpreter (`IntTaskData`) evaluates this until the ML runtime is fully initialized.
3. Once native code is available (via compilation or loading), the interpreter is generally not used for production code.

### Shared Object Model

Both bytecode and native code share:
- **Bottom-bit tagging** for integers: `TAGGED(x)` shifts the value left and sets bit 0 to 1.
- **Object layout**: A length word followed by data (either PolyWords or bytes).
- **Exception model**: Same on-stack handler chain and exception packet mechanism.
- **Allocation**: Same `allocPointer` / `allocLimit` protocol.

### Bytecode Interpreter Structure

The `IntTaskData` class mirrors `Arm64TaskData`:
- `stackItem *taskSp`: Interpreter stack pointer.
- `stackItem *hr`: Handler register.
- `stackItem *sl`: Stack limit.
- `PolyWord exception_arg`: Exception packet.
- `PolyWord interpreterPc`: Current bytecode address.

The bytecode is a sequence of opcodes (defined in `int_opcodes.h`, not surveyed in detail). Each opcode manipulates the stack and may call into the RTS (e.g., allocation, arithmetic).

### Consequence for Rewrite

If you are rewriting the runtime in Rust and plan to keep the bytecode interpreter:
- The interpreter must maintain the same interface (exception model, allocation, GC scanning).
- The bytecode format is immutable (it's part of the persistent image format).
- Cranelift targets will replace the interpreter for hot code paths but cannot eliminate it entirely.

---

## Summary of Key Dependencies and Rewrite Implications

| Subsystem | Cranelift Impact |
|-----------|------------------|
| **1:1 Threading** | Must bind each ML thread to one Rust task/thread; no green threads. |
| **TaskData with AssemblyArgs** | Must create an equivalent Rust struct holding heap pointers, stack pointers, and exception state. X26 must always point to this struct in native code. |
| **RTS Call ABI** | Cranelift must emit code that passes thread ID in X0, marshals arguments per AAPCS, and calls extern functions by symbol name. |
| **Allocation Overflow** | Cranelift must emit prologue checks and call a fixed `heapOverFlowCall` trampoline when exhausted. |
| **Signal Handling** | Per-thread signal stacks and thread-local `TaskData` lookup; no signal-driven traps (those are explicit checks in code). |
| **Exception Handling** | On-stack handler chain, not tables. Each `handle` frame must be explicitly managed. Exceptions raised from RTS must set `exceptionPacket` field. |
| **FFI** | Release ML-memory lock before calling C; reacquire after return. No automatic callback generation; compiler must emit wrappers. |
| **Bytecode** | Keep the interpreter for bootstrap; Cranelift code coexists with it but uses native execution for production. |

---

## Unclear or Sparse Areas

1. **Exact callback wrappers**: The code does not show where callbacks are generated or how the C function signature is translated to a wrapper. The compiler (not the RTS) likely handles this.
2. **libffi absence**: It is surprising that PolyML does not use libffi. Either callbacks are hand-coded, or the compiler generates them inline.
3. **Null-pointer and allocation traps**: The code checks for these explicitly rather than using signals, making the design simpler but less efficient than systems that use SEGV-based allocation.
4. **Signal handler specifics**: `sighandler.cpp` is partially surveyed; full details of how profiling signals are handled and how user handlers are dispatched are not fully clarified here.
