# Hard problems

For each: **problem statement → options → recommendation → risks**.

Web-search references (May 2026):
- Stack maps: Bytecode Alliance, *New Stack Maps for Wasmtime and Cranelift* (fitzgen.com/2024/09/10)
- Tail calls: bytecodealliance/wasmtime PR #8540, default-enabled on x86_64 / aarch64 / riscv64
- Exceptions: cfallin.org/blog/2025/11/06/exceptions/

---

## 1. GC safepoints and stack maps with Cranelift

### Problem

PolyML's runtime needs precise GC roots from compiled-code stack
frames at any point a thread can be stopped. Today this works because
the existing X86/Arm64 backends emit frames with a fixed,
runtime-known layout (see `notes/boundaries.md` §1.3). Cranelift will
allocate registers and stack slots freely — the runtime cannot infer
where the pointers are.

### Options

**A. Use Cranelift's *user stack maps*.** The Cranelift user marks
specific SSA values as "GC reference"; cranelift-frontend performs
liveness, inserts spills/reloads around safepoints, and annotates
each safepoint with the precise stack-slot offsets containing live
references. Stack maps are emitted at binary emission time. Alias
analysis still operates around the spills (so RLE/forwarding is
unaffected).

**B. Constrain Cranelift to a fixed frame layout.** Hand-pick the
register allocation, pin specific roles to specific physical regs,
emit prologues that match PolyML's existing convention. The runtime
can then walk frames the same way it does today.

**C. Use conservative scanning.** Inspect every word in a stack
frame; if it looks like a pointer, treat it as one. Used by Boehm GC
etc. Doesn't fit PolyML — tagged ints with bottom bit set are easily
distinguishable, but pinned bytes might masquerade as pointers.

### Recommendation: **A — user stack maps**.

Cranelift's API matches the use case very closely. It's been
production-tested in Wasmtime for `externref` GC. We'd:
1. Compile `BIC` such that any value of `GeneralType` is marked
   `r64` (or `r32` for 32-in-64).
2. At every `BICEval`, `BICAllocateWordMemory`, function entry/exit,
   and back-edge — emit a safepoint.
3. Consume the resulting stack-map table at runtime in a sidecar
   structure indexed by `pc`.

### Risks

- Cranelift's stack-map mechanism may not place safepoints exactly
  where we want them. Need to spike this early — write a tiny
  function with explicit safepoints, dump the stack map, verify
  it covers the expected sites.
- The 32-in-64 case (compressed pointers) requires marking values as
  `r32`, not `r64`. Need to confirm cranelift supports `r32`
  references on 64-bit targets, or fall back to never using 32-in-64
  in the Cranelift backend (acceptable; 64-bit native is the
  common case).
- Performance: the new user-stack-maps approach is *better* than the
  old for alias analysis, but every safepoint forces spills.  We
  should sparingly mark only true safepoints.

---

## 2. Proper tail calls

### Problem

ML demands proper tail calls. PolyML lowers `BICLoop` (inline
tail-recursion) to plain jumps and `BICEval` in tail position to an
optimised tail call (stack-frame reuse). Cranelift must support both.

### Options

**A. Use Cranelift's `tail` calling convention.** A non-C-ABI calling
convention specifically for tail-call-heavy code. Default-enabled on
x86_64, aarch64, riscv64 as of 2024+. Same convention required on
both caller and callee. Has explicit support for "tail call" semantic
(stack-frame reused).

**B. Bounce trampoline.** Each tail call returns the *next* function
to call to a tiny scheduler loop that dispatches it. Used by some
Scheme implementations on platforms without tail calls. Slow.

**C. Continuation-passing-style transformation.** Pre-CPS every ML
function so calls are explicit continuations. Significant compiler
work; doesn't compose with PolyML's existing IR.

### Recommendation: **A — Cranelift `tail` CC**.

Cranelift's `tail` convention covers all three Stage-1 targets
out of the box. Inline `BICLoop` lowers to a CLIF block back-edge
(plain jump). Tail-position `BICEval` lowers to a `return_call`-style
op under the `tail` convention.

### Risks

- The `tail` CC is **not ABI-stable**; callees and callers must agree.
  That's fine within ML code (all closure calls use it) but the
  boundary with RTS calls (C ABI) is a transition point — at every
  call to a runtime function we'd switch CC for the call, then back.
  Need to plan the trampoline shape.
- `tail` CC interacts with `try_call` exception support — we don't
  use Cranelift exceptions, so no conflict.
- Some niche `BICEval` cases (calls to closures with non-`GeneralType`
  args/return) may exercise corners of the `tail` CC. Worth testing.

---

## 3. Pointer tagging across word sizes

### Problem

PolyML's value representation is bottom-bit tagging: bottom bit 1 ⇒
tagged int; bottom bit 0 ⇒ object pointer (word-aligned). The maximum
tagged int therefore depends on word size:
- 32-bit: signed values in `[-2^30, 2^30 - 1]`
- 64-bit: signed values in `[-2^62, 2^62 - 1]`
- 32-in-64: same as 32-bit (32-bit values stored in 64-bit slots)

Values outside that range box into arbitrary-precision integers. A
heap image written on 64-bit *cannot* be loaded on 32-bit if any
tagged int exceeded the 32-bit range. Conversely, a 64-bit image
ingesting a 32-bit heap could trivially widen tagged ints.

### Options

**A. Word-size as a hard image dimension.** Maintain separate 32-bit
and 64-bit heap images; only target the 64-bit (and optionally 32-in-64)
case in `polyml-rs` Stage 2. Defer real 32-bit native.

**B. Re-tag at load.** Walk every heap word at load, re-tag based on
target word size, box overflowing ints. Expensive (~O(heap), one-time)
but enables one image → multiple word sizes.

**C. Always box integers in the portable image format.** The portable
image's tagged ints become explicit boxes; load-time decoder re-tags
into native form. Image bigger; loader simpler.

### Recommendation: **A for Stage 2; reassess after Monday milestone**.

For initial bring-up, just target 64-bit native (and possibly 32-in-64
on x86_64). 32-bit support is a Stage-3+ concern; it's been the
default-but-secondary target for PolyML for years anyway. If/when we
add a 32-bit target, the choice becomes B vs C.

### Risks

- Some basis library calls bake in word-size assumptions. Likely the
  compiler frontend (in SML) handles this; we shouldn't have to.
- `BICArbitrary` codegen must respect the target's `MAXTAGGED`. Need
  to thread word size as a codegen parameter — but it's already there
  via the architecture selection.

---

## 4. Exception unwinding through Cranelift frames

### Problem

PolyML exceptions are an on-stack handler chain (`notes/boundaries.md`
§1.6). `BICHandle` pushes a handler frame; `BICRaise` walks the chain
and jumps to the matching handler PC after restoring SP. No platform
unwinder. Cranelift recently added `try_call`-based exception support
but it's Linux-only and uses platform unwinding tables.

### Options

**A. Don't use Cranelift exceptions.** Lower `BICHandle` and `BICRaise`
directly: push/pop a handler frame in CLIF, raise walks the chain via
loads + jumps. From Cranelift's perspective these are just memory ops
and indirect jumps.

**B. Adopt platform unwinding.** Restructure ML exceptions so each
`BICHandle` becomes a `try_call` and exception data flows through
platform unwinder. Major change to the runtime, breaks
interpreter compatibility (interpreter uses the same on-stack chain),
limited to Linux today.

**C. Hybrid.** Native code uses platform unwinding; interpreter uses
chain; interop costly.

### Recommendation: **A — keep the on-stack handler chain**.

This is the lowest-risk path. The chain is the existing convention; the
interpreter uses it; the runtime knows how to walk it. From Cranelift's
perspective it's plain code, no special facility.

### Risks

- The "raise" path walks the handler chain past any number of
  Cranelift-generated frames. Each of those frames may have live GC
  references in stack slots — they're discarded by `raise` without
  the GC seeing them as roots again. Need to confirm this is safe
  (it is, in PolyML today: `raise` adjusts SP atomically, frames are
  abandoned). For GC interaction: as long as we don't `raise` *into*
  a GC pause, we're fine. Safepoints don't trigger on raise.
- If Cranelift's regalloc puts a live GC reference in a callee-saved
  register, and an inner frame raises, that reference is "trapped"
  in the abandoned frame and becomes garbage. Correctness-wise that's
  fine (the value is logically unreachable). But it means we don't
  *need* to walk abandoned frames for the GC.

---

## 5. Architecture-portable heap images

### Problem

Today's pexport format encodes its source architecture and is not
truly portable across arches — except in the special case of the
interpreted backend, where `bootstrap64.txt` runs on any 64-bit target
via interpretation. We want heap images that load cleanly on
x86_64 / aarch64 / riscv64 without per-arch builds.

### Options

**A. Store BIC (backendIC IR) in the portable image; codegen at load.**
Most compact. Loader includes Cranelift. Compile time at load (could
be slow for big images). Loaded images can be re-cached natively after
first load (an `image_for(target_arch)` companion file). The IR is
stable-ish, owned by us.

**B. Store CLIF (Cranelift IR) in the portable image.** Lower-level
than BIC; bigger images. Cranelift IR is *not* a stable format —
versioned with Cranelift. Bumping Cranelift would mean rebuilding
every portable image.

**C. Store bytecode; interpret or JIT.** Extends the existing
`MA_Interpreted` pattern. Interpreter pays per-run cost. JIT at first
use via Cranelift is reasonable.  Requires the bytecode interpreter as
runtime dependency.

**D. Store machine code for every supported arch in fat images.**
Like macOS fat binaries. Larger; no load-time codegen. Production
deploys could ship arch-specific thin images.

**E. Store both: heap data is portable; code is rebuilt from BIC.**
Hybrid. Data structures use a portable encoding (explicit word size,
endianness fields, tagged-int rules); code is regenerated at load.
This is the heap-image agent's recommendation.

### Recommendation: **E — hybrid (portable data + rebuilt code from BIC)**.

Concretely:
- Heap image has a header declaring word size, endianness, and tagging
  rules
- Object-graph regions are portable (PolyWord stored as a discriminated
  union: `Tagged(i64) | Pointer(id)`, with `id`s resolved at load)
- Code objects in the portable image carry their *BIC body*, not native
  bytes. At load, Cranelift compiles each one for the target arch.
- A side-format (`image.native.<arch>.cache`) optionally caches the
  compiled-code result for fast subsequent loads.

### Risks

- BIC is internal to PolyML's compiler. We'd be embedding compiler IR
  in a runtime artifact. That's a versioning headache: if `BIC` evolves,
  old images break.
- Mitigation: stamp a version into the image header; the loader
  refuses incompatible versions, prompts a recompile.
- The hybrid format is *new code*. The existing pexport reader doesn't
  understand BIC. We'd write a new reader/writer pair.
- Load time for big heap images becomes Cranelift-bound. Probably OK
  given Cranelift's speed, but worth measuring.

---

## 6. Bootstrap

### Problem

The SML compiler is itself in SML. To get a native compiler on a new
target, you need an existing compiler that works on that target. The
existing solution is `bootstrap64.txt` — an interpreted-backend image
that runs on any 64-bit target via the bytecode interpreter
(`notes/bootstrap.md`).

For us, we have a chicken-and-egg variant: we want the new Rust
runtime to load and run the SML compiler so we can use its codegen
seam — but the runtime needs to be at least minimally working
*before* it can load the compiler.

### Options

**A. Port the bytecode interpreter to Rust verbatim.** Then load
`bootstrap64.txt` and let the compiler run on our interpreter, just
as today. Once the Cranelift backend exists, run Stage2..7 to produce
a native heap image. Bootstrap path identical to upstream.

**B. Skip the interpreter; use upstream PolyML as a build-time
dependency.** During the build of `polyml-rs`, invoke upstream
`poly` to produce a pre-compiled heap image targeted at our new
backend. No interpreter in Rust at all. Fast for early bring-up;
sketchy for cross-compilation; punts on the architecture-portability
story.

**C. Compile bytecode → Cranelift IR at runtime.** A Cranelift-based
"interpreter" that JITs bytecode opcodes. Works once Cranelift is
reliably integrated, but creates a dependency: Cranelift backend must
be working before *anything* can run, including the rest of the
runtime.

**D. Begin from a partial port.** Start with just enough of the
bytecode interpreter to load a *minimal* test heap image (no full
compiler), and bring up the rest of the runtime in parallel.

### Recommendation: **B for Stage 2, then A for Stage 3**.

For the Monday milestone and early Stage 2: use upstream PolyML to
compile small SML programs to pexport heap images, target the new
Rust runtime. This lets us validate the runtime↔codegen interface
without needing a working interpreter.

Once that's stable, do option A — port the bytecode interpreter — to
unblock real bootstrap-on-new-arch.

### Risks

- (B) bakes in a cross-compile dependency: building polyml-rs requires
  having upstream poly available for the host arch at build time. Awkward
  for CI on rare arches.
- (A) is significant work — the interpreter is non-trivial; estimate
  multiple weeks.
- The interpreter's calling convention with the runtime is currently
  C++-specific; we'd port that interface too. Wraps around the same
  TaskData boundary, so it should be possible to share with the native
  codegen.

---

## 7. (Bonus) License posture

Not asked, but discovered during Stage 1 and Stage-2-blocking.

PolyML is **LGPL 2.1**. We have three components in play:

| Component | License posture |
|---|---|
| New Rust runtime (`polyml-rs`) | Clean-room rewrite. Can be permissive (MIT / Apache-2.0). |
| Cranelift backend | New code. Permissive. |
| Bootstrap heap image | LGPL 2.1 (compiled output of LGPL source). |

### Options

**A. Permissive runtime; LGPL bootstrap shipped separately.** Main
`polyml-rs` repo is MIT/Apache. The bootstrap image lives in a
sibling repo (or downloaded at build time from upstream PolyML)
and remains LGPL. Combined distribution = LGPL.

**B. All-LGPL.** Accept that the runtime is effectively LGPL because
it's designed-to-work-with the LGPL compiler. Simplifies licensing
discussions, complicates downstream adoption.

**C. Full clean-room SML implementation.** Don't use PolyML's compiler
at all; write our own. Years of work.

### Recommendation: **A**.

Compatible with most downstream users; explicit about the boundary.
Requires either a downloader at build time (fetches `bootstrap64.txt`
from upstream) or a clearly-LGPL sidecar crate.

### Risks

- Distribution channels (crates.io, package managers) may not love
  build-time-fetch. Need to test.
- Some users will be confused by the dual-license arrangement.
