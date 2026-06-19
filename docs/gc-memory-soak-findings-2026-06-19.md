# GC + memory-safety soak — findings (2026-06-19)

> **CORRECTION (2026-06-19, the fix workflow wf_e2bd8923-916).** The "root cause"
> below is PARTLY MISATTRIBUTED. Forensics during the fix (gdb + a from-space
> tripwire) showed the reproducer's *SIGSEGV* was actually a **harness bug**: the
> `gc_tiny_heap_stress` example never registered the image's MUTABLE space as a GC
> root (the real CLI always does — `main.rs:340-353`), so an image-mutable word
> pointing into the alloc-space couldn't be forwarded, dangled when collect freed
> from-space, and `INDIRECT_LOCAL_B0` later derefed it. So the *crash* was never
> reachable via `poly run` (which registers the root) — it was an incomplete
> reproducer. SEPARATELY, the below-sp dangling-pointer hazard described below IS
> real but **latent/non-crashing** (44 residuals on the reproducer, ~26831 on a
> basis load — overwritten before re-deref in practice). The fix landed BOTH: the
> example now registers the root (kills the reproducer SEGV), and the GC now scrubs
> `[0,sp)` to `Tagged(0)` on each collect + the audit is widened to `[0,len)`
> (closes the latent below-sp hazard + makes the detector honest). Both are real,
> sound, byte-identical; commit forthcoming. Read the rest with this correction in
> mind — the below-sp analysis is accurate as a *latent hazard*, not as the
> reproducer's proximate crash cause.


Dedicated stress round on the memory layer (Cheney GC + image writer), the one
runtime area without a prior dedicated round and the scariest bug class.
ultracode wf_0eab2712-02c (20 agents). Three angles: GC-audit, leak/soak, export
round-trip. **One real bug found** (a GC use-after-free + a detector blind spot);
export + leak sides clean.

## Verdict

| Angle | Result |
|---|---|
| GC-audit (residual from-space pointers) | **BUG: use-after-free + detector blind spot** (latent, not reachable via `poly run`) |
| Leak / soak (RSS over sustained allocation) | clean — flat post-GC working set, constant RSS floor |
| Export round-trip (load→export→reload→compare) | clean — byte-identical fixpoint `export(reload(export(x)))==export(x)`, export-after-GC stable; `export_roundtrip` 2/2 + `export_roundtrip_fuzz` 12/12 pass |

## The bug: GC use-after-free (heap corruption → deterministic SIGSEGV)

**Root cause.** The Cheney collector FORWARDS roots, and `POLYML_GC_AUDIT` CHECKS,
only stack slots **`[sp, len)`** (the GC forward loop `interpreter/mod.rs:709`
`for i in sp..stack_len`; the audit `audit_no_residual_from_space_ptrs`
`mod.rs:846` `for i in self.sp..self.stack.len()`). Slots **below `sp`** are the
free/garbage region `drop_n`/`RESET` bump `sp` past, leaving stale values *by
design* (`mod.rs:704` "Below sp is free"). Those stale values can be live-from-the-
past pointers into **from-space**. `gc::collect`'s `replace_storage`
(`gc.rs:388/413`) drops/frees the from-space `Box` unconditionally — so the
below-`sp` pointers now **dangle** (point into freed memory). When a later
`sp`-lowering op re-exposes one and the dispatch loop dereferences it →
use-after-free.

**Detector blind spot.** `POLYML_GC_AUDIT=1` reports CLEAN on the faulting run
(zero `GC AUDIT:` lines) because it shares the `[sp, len)` scan. A throwaway
full-stack `[0, len)` audit (added then reverted; tree pristine) found 44 residual
from-space pointers below `sp` at the crash collect — each value inside the
just-freed range. gdb pinned the fault at `mov (%rdx),%rdx` in the dispatch loop,
`rdx == si_addr` inside the freed from-space `Box`.

**Reproducer** (deterministic, 5/5 exit 139):
```
cargo build --release -p polyml-runtime --example gc_tiny_heap_stress
POLYML_GC_AUDIT=1 POLYML_GC_THRESHOLD=50 POLYML_GC_QUIET=1 \
  ./target/release/examples/gc_tiny_heap_stress 131072 2000000
# "GC: 65538 -> 26276 words (40% retained)" then SIGSEGV.  ~40% retained (not
# exhausted; space.alloc would panic on real OOM) => genuine corruption, not OOM.
```
A heap-size sweep: SEGVs only at the 1 MB (131072-word) heap; **clean at ≥2 MB**
even over 20M steps (the freed pages aren't reused before the dangling deref).

## Reachability — LATENT, not reachable via `poly run`

The CLI **always** allocates a fixed 1.6 GB (or 256 MB) alloc-space `Box`
(`main.rs:342/349/779/979/1077`); `POLYML_GC_THRESHOLD` changes only *when* to
collect, never the `Box` size. So no supported `poly run` invocation can build a
heap small enough to hit the page-reuse window — verified: real
`poly run bootstrap64.txt` at `THRESHOLD=1` does **0** GC cycles and returns
`Tagged(0)`. Triggering it needs `with_default_alloc_space_words(<~2M)`, which only
test/library code does today.

**But the below-`sp` residuals are NOT a tiny-heap artifact** — they are real in
production-sized runs too: with ASLR disabled, the genuine **basis load** leaves
**26831** residual from-space pointers below `sp` at its single GC collect
(`104857600 → 1607669 words`), 3/3, while still completing `Tagged(0)`. The bug
survives only because those dangling pointers happen to be overwritten (or the
1.6 GB `Box`'s freed pages not reused) before any re-deref. This is the deferred
"GC alloc-retry heap-corruption hazard" class (foundation audit).

## Candidate fixes (HANDS-ON — GC-internal, NOT auto-applied)

Left for a focused review on a quiescent tree; the soak fleet correctly did **not**
touch GC code. Options, with trade-offs:
1. **Scrub below-`sp` slots to a tagged sentinel** (`Tagged(0)`) on `drop_n`/`RESET`
   (or on collect, over `[0, sp)`). Eliminates the dangling pointers. Cost: a
   hot-path write (`RESET_1` is ~3% of dispatches) if done eagerly per-drop; cheaper
   if done once per collect over `[0, sp)`.
2. **Forward `[0, len)` in the collector** — keeps below-`sp` pointers valid, but
   risks keeping garbage alive *and* mis-forwarding non-pointer junk (a tagged int
   bit-pattern that looks like a from-space address). Riskier.
3. **Keep from-space mapped / pooled** instead of dropping the `Box` (matches
   upstream PolyML's space recycling) — the dangling pointers stay valid memory
   (stale but not freed). Biggest change; most faithful to upstream.

**Detector fix** (do alongside): widen `POLYML_GC_AUDIT`'s scan to `[0, len)` so it
stops being blind to this class. NOTE it will then FIRE on real forced-GC workloads
(below-`sp` residuals are the NORM) — so first decide whether a below-`sp` residual
is a *violation* (the slot could be re-exposed) or *benign garbage* (the interpreter
guarantees re-exposed slots are written before read — which the bug shows is NOT
currently guaranteed).

## What was banked from this round (test/runner only — no GC code)

- `examples/gc_tiny_heap_stress.rs` — the standing UAF reproducer.
- `tests/export_roundtrip_fuzz.rs` — 12 export-after-GC / normalization tests (all pass).
- `export_roundtrip_live.rs::gc_audit_smoke_basis_load` — `#[ignore]` smoke: real
  basis load under `POLYML_GC_AUDIT=1`, asserts `Tagged(0)` + no residual line +
  ≥1 collect (pins the *tracked-state* invariant on the heaviest GC-firing workload).
- `regression.sh` — wired the export round-trip targets into FAST + `export_roundtrip_live`
  into FULL.
- the `run_until` step-count-on-error fix (reports executed steps even when a run
  faults — cosmetic, semantics-identical; the reproducer relies on it).

A tiny-heap UAF regression test should be added **after** the collector fix lands
(it currently SEGVs by design).
