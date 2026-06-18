# JIT feasibility deep-dive — findings (2026-06-18)

Evidence-based answer to: *can the Cranelift JIT beat the tuned interpreter?* (the
gate for `bicimage`, the native-code-speed portable image). Workflow wf_d6d6e506-2e5
(measure → decisive experiment → verdict). The experiment's measurement code was
deliberately **MEASURE-ONLY** scaffolding and has been reverted; this doc is the
deliverable.

## Verdict: the JIT CAN win (modestly) — the prior "JIT cannot win" is REFUTED

The earlier conclusion ("JIT ~5% slower, coverage wall, uncertain payoff → bicimage
dead") was reasoning from the **default install set**, which is the *cold periphery*.
Actually installing the **hot** functions flips it:

| Install set | basis-load user-CPU (median of 3, interleaved) | vs interp |
| --- | --- | --- |
| interp (no JIT) | 16.18 s | — |
| `--jit` stock (727 cold-periphery installs) | 16.99 s | **−3.9% (slower)** ← the prior finding |
| +#1 hottest fn (7.4% of steps) → 728 | 15.88 s | **+2.9% faster** |
| +#1,#3,#6,#10,#11 (~18% step coverage) → 731 | 15.46 s | **+4.7% faster (1.047×)** |

All produce `Tagged(0)` clean returns. So the JIT measurably beats the interpreter
once genuinely hot functions are installed.

## The boundary is NOT the wall

The decisive unknown was the per-call interp→JIT trampoline cost. **Measured: 35.6
ns/call** (128 cycles @ 3.6 GHz; reproduced 35.0–35.7). Decomposition: `args_buf`
`Vec` alloc 6.1 ns + SipHash `jit_cache` probe (727 entries) 8.9 ns + JIT_INTERP TLS
swap + indirect call (raw native call floor 1.7 ns) + result push.

**Crucially, the interpreter's own call+frame setup is 42 ns — so the JIT boundary
(35.6) is *cheaper* per call than an interp frame.** Optimistic crossover = 7.3
interp-steps/call to amortize; the average hot function does **37.5 steps/call**
(1.784B steps / 47.6M calls), far above crossover. Physics is not the wall.

## The real blockers (tractable correctness/engineering, not physics)

1. **The install filter has a FALSE-POSITIVE bug.** It rejects functions whose
   bytecode `contains(&0x16)` as having `CALL_LOCAL_B` — but `0x16` also occurs as
   an *immediate byte* of `CONST_ADDR16_8`/`CONST_ADDR8_8`. The #1 hottest function
   (632 bytes, 7.4% of all steps) is rejected on two such immediate bytes (offsets
   95, 608); an instruction-boundary disasm walk confirms **zero real CALL_LOCAL_B**.
   When installed (defeating the false positive), it runs correctly through the full
   basis load to `Tagged(0)` with 100% JIT cache hits on that function. **Fix:
   make the filter instruction-boundary-aware (a disasm walk, not a raw byte scan).
   Cheap, safe, immediate — installs the single biggest hot function.**

2. **Non-monotonicity: naive "install all hot" REGRESSES.** Function #4 (3.6% of
   steps, makes many *outgoing* trampolined calls) is a **net LOSS** (+1.6 s) when
   JIT'd — every outgoing call pays the `Vec`-allocating `closure_call_trampoline`.
   **Fix: a per-function net-benefit install gate** (don't install functions whose
   outgoing-call density makes them net-negative under the current trampoline).

3. **`CALL_CONST_ADDR` SEGV is an unisolated multi-function INTERACTION bug**, not a
   per-function impossibility. Trust-all (727→1959) SEGVs at 3.77M steps; curated/
   isolated installs (the 5 hot CCA functions) are **correct + fast** to `Tagged(0)`.
   Root-causing it unlocks ~22% of hot steps. (Deferred — harder.)

## Ceiling

Realistic ~**1.3–2.0×** *if* every hot function were net-positive; **demonstrated
1.05× at ~18% coverage**. But #4 proves some hot functions are net-negative under the
`Vec`-allocating trampoline, so true full coverage won't reach the optimistic ceiling
without lowering the per-call cost. This is **modest**, not the "native-code speed"
the bicimage pitch implies.

## Path to bicimage (gated, staged)

**Do specific JIT work FIRST; do not greenlight bicimage yet, do not shelve it.**

**PHASE 0 (~1 week, low-risk, makes `--jit` not-a-regression regardless of bicimage):**
1. Instruction-boundary-aware install filter (kills the #1 false positive).
2. Per-function net-benefit install gate (kills the #4-class regression).
3. Lower the boundary: replace the per-call `args_buf` `Vec` with a stack array, and
   swap `jit_cache`'s SipHash for FxHash/a pointer-map (~halves the 35.6 ns → lowers
   crossover, likely makes #4-class functions net-positive).

**Then re-measure.** If curated installs hold a robust *monotone* speedup, do the
harder coverage work (root-cause the `CALL_CONST_ADDR` interaction SEGV; solve
`CALL_LOCAL_B`/`CALL_CLOSURE` arity) **behind a measured >1.5× gate** before building
the bicimage spec/writer/reader/cache. The portable image is *already* arch-neutral
(pexport); bicimage adds only per-arch JIT-on-load + a cache, so the format delta is
small — **the value is entirely in the JIT being fast.**

## If the trampoline JIT can't clear >1.5× (the likely ceiling)

Routes to native-speed portable images that don't trampoline back per call:
1. **Whole-function/whole-region compilation** — keep nested calls IN native code
   (compile a function + directly-call its JIT'd callees). Converts the boundary from
   per-call to per-region-entry; fixes the #4-class problem at the root. Highest
   leverage. Needs call-site arity resolution (CALL_LOCAL_B/CALL_CLOSURE).
2. **Direct JIT→JIT calls** (thin native ABI, no Vec/TLS) — prerequisite for (1).
3. **Threaded-code/computed-goto dispatch in the interpreter** — speeds ALL code (no
   coverage problem), raises the 110M-steps/sec baseline. Lower-risk, but makes the
   interpreter *harder* to beat (works against bicimage); the better bet if the goal
   is "faster portable images" generally rather than "native speed specifically."
4. **AOT-compile-on-load with a self-contained native ABI** (side-exit to interp only
   for untranslatable opcodes, not per call) — bicimage's logical endpoint, the only
   design that plausibly reaches real native speed; largest effort (months).

## Bottom line

The bicimage *speed premise* is **empirically alive** (no longer dead): the JIT beats
the tuned interpreter today on curated installs, and the boundary is cheaper than an
interp frame. But the win is currently **modest (single-digit %)**, gains are
**non-monotone**, and the pexport we already ship is portable + fast-to-load. So:
land Phase 0 (cheap, de-risks `--jit` regardless), re-measure, and gate bicimage on a
demonstrated >1.5× — otherwise pursue whole-region compilation (the real road to
native speed) or accept the (already excellent, already portable) interpreter.
