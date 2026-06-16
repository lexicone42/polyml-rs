# Release-readiness code review — 2026-06-16

Read-only review (4 per-crate reviewer agents + a cross-cutting manifest pass)
toward a shareable repo. Findings are distilled; severity is BLOCKER (fix before
sharing) / SHOULD-FIX / NICE-TO-HAVE. Status column tracks what's been banked.

## Cross-cutting (manifest / workspace) — DONE

- repository URL `bryanw` → `lexicone42/polyml-rs`; `polyml-jit` `description`
  added (commit dbda72f). version stays 0.0.0 until a release tag. No
  keywords/categories/readme (optional crates.io polish).
- `[profile.release]` comment says "with overflow checks" but sets
  `overflow-checks=false` (the `release-debug` profile has them) — stale comment,
  harmless (SML `Overflow` is implemented explicitly, not via Rust overflow-checks).

## polyml-image (pexport) + polyml-bin (CLI)

**BLOCKER**
- **Allocation amplification in pexport** (`pexport.rs:386` `read_hex_bytes`,
  `:654` `parse_value_list`): `Vec::with_capacity(n)` with `n` parsed directly
  from the file, no cross-check vs remaining input. A ~20-byte file
  (`…0:S9999999999|`) triggers a multi-GB alloc/OOM before reading any payload —
  classic decompression-bomb. Fix: bound `n` by remaining bytes (`2n` for hex,
  `n` for value lists), or drop `with_capacity` and let the bounds-checked
  `bump()?` loop grow naturally. *The one true blocker for "don't die on a bad image."*

**SHOULD-FIX**
- CLI `run`/`diff`/`disasm` deref the image root as a code pointer WITHOUT the
  `is_closure_object`+`is_data_ptr` guard that `load` already has (`main.rs:321`,
  `:745`, `:937`) → SEGV on a parse-valid-but-malformed image. Gate them like `load`.
- `parse_object_line` skips to EOL after the body (`pexport.rs:618`), silently
  accepting trailing garbage; assert next byte is newline/EOF.
- `parse_entry_point` `start + n` can overflow on a hostile count (`pexport.rs:774`)
  → panic on bad input; use `checked_add`. (Subsumed by the alloc-bound fix too.)
- `read_u64`/`read_i64` `from_utf8(...).unwrap()` (`pexport.rs:344`,`:377`) — sound
  today via a precondition set lines away; fragile. Use `from_utf8_unchecked` or
  map to `BadNumber`.
- `--use` vs stdin "mutually exclusive" documented but unenforced; `/dev/null`
  redirect silently no-ops on open failure (`main.rs:287`,`:434`).

**NICE-TO-HAVE**
- Stale CLI text: `about = "...(work in progress)"`, header "not at transfer-control
  yet — Phase 2.1", and `load` prints "execution not implemented yet" (`main.rs:24`,
  `:1-6`, `:689`) — all false now (runtime executes the bootstrap + HOL4/Isabelle).
- Dev/JIT-forensics subcommands (`diff`/`disasm`/`--scan-isolated`) exposed as
  top-level peers of `run`/`inspect`; `--scan-isolated` has `to_str().unwrap()`
  (`main.rs:1073`, non-UTF-8 path panic). Hide behind a `dev`/feature group.
- exit-code `clamp(0,255)` maps `exit ~1` to 0; use `& 0xff` for POSIX semantics.
- `write` emits non-ASCII arch byte via `char` formatting → breaks round-trip for
  `SourceArch::Other` (`pexport.rs:421`). Niche.
- Recommends a `cargo-fuzz` target on `Image::parse` — would find the alloc-amp +
  overflow findings in minutes. Strong suggestion for release.

## polyml-runtime interpreter core

No BLOCKER (no memory-safety hole reachable from *trusted*, compiler-emitted
bytecode; the documented RESET_N vs RESET_R_N hazard is correctly handled, with a
guard test). Findings are adversarial-input + a real faithfulness bug:

**SHOULD-FIX**
- **JUMP32 family treats the 32-bit offset as UNSIGNED; upstream sign-extends**
  (`mod.rs:2908-2932` vs bytecode.cpp:2236) → a backward JUMP32 becomes a ~4 GB
  forward jump. A genuine faithfulness bug; latent because it only fires in
  functions >64 KB needing a *backward* 32-bit jump (bootstrap/HOL4/Isabelle don't
  hit it, so the oracle never caught it). Fix: `((hi<<16)|lo) as i32 as isize`.
- `allocate()` (`mod.rs:3052`) panics (aborts) on heap exhaustion — a non-panicking
  `try_alloc` exists unused right beside it. ALLOC_WORD_MEMORY (`:1407`) takes the
  length from the stack → a malformed image can force the panic. Route through
  `try_alloc` → an `OutOfMemory` error.
- DELETE_HANDLER / RAISE_EX / do_raise_ex (`:1844`,`:1877`,`:3776`) read the handler
  frame via direct `stack[sp]` indexing after `sp += 1`; a corrupt `handler_sp` can
  index past the end → panic (DELETE_HANDLER has no length guard). Validate
  `handler_sp + 1 < len`.
- The `GC roots: …` eprintln (`:715`) is NOT gated by `POLYML_GC_QUIET` (the
  per-cycle `GC:` line is) — breaks the documented quiet contract.
- Stale doc on `real_to_int_round` (`:3423`): says "half away from zero" but code
  correctly does `round_ties_even` (banker's; differential-tested). Fix the doc.

**NICE-TO-HAVE**
- Stale comments contradicting code: `CALL_FAST_RTS` "stubbed … no RTS yet" (`:1506`)
  but `rts_call` fully dispatches; `GET_THREAD_ID` TODO reads as missing (it's
  single-threaded *by design*). `opcodes.rs:290` `read_u16_le` pub, no bounds.
  `reset_stack` sets `handler_sp=0` (inconsistent with the `len()` "no handler"
  sentinel). Defensive `process::abort()` calls behind debug env flags (sharp edge
  for embedders). `do_call`/`do_tail_call` print 40+ stderr lines on the error path
  unconditionally.
- OBSERVATION (cross-cutting): ~30 opcode handlers deref raw pointers/offsets taken
  from stack PolyWords under a "compiler emits valid offsets" invariant — sound for
  Poly/ML-produced images, but **loading an untrusted/corrupt image is not
  memory-safe**. Needs an explicit threat-model statement in the README (also
  flagged by the image reviewer).

## polyml-runtime memory / RTS / GC

No unconditional BLOCKER. Confirmed: the 3 `jit_dispatch_*` `unsafe fn` markings are
complete/consistent; EntryPoint sizing math is exactly tight (no overrun).

**SHOULD-FIX**
- **GC untracked from-space pointer = silent use-after-free** (`gc.rs:140`,`:354`):
  if `forward_impl` finds a from-space address matching no object, it logs and
  returns WITHOUT updating the slot; after `replace_storage` drops the from-space
  box, that slot dangles. Only `POLYML_GC_AUDIT=1` (opt-in) detects it. Make a
  non-empty `untracked_addrs` a hard error rather than eprintln-and-continue.
- pexport `vec![None; n_objects]` (`:454`) from an unvalidated u32 header → multi-GB
  OOM on a malformed header. Cap `n_objects` vs remaining input. (Same DoS class as
  the image-reviewer's `with_capacity` BLOCKER — both confirmed independently.)
- RTS/loader allocations use panicking `space.alloc` (`rts.rs` bignum/real sites,
  `loader.rs:202`) but GC only fires at the top of `step()` — a single large IntInf/
  Real result panics instead of GC-and-retry (the documented "alloc-retry deferral").
  Convert hot bignum/real allocators to `try_alloc` + raise an SML size exception.
- `poly_shift_left_arbitrary` (`rts.rs:2208`): unbounded shift amount → unbounded
  BigInt alloc (`IntInf.<<(1, hugeN)`). Sanity-cap before allocating.

**NICE-TO-HAVE**
- `find_object` saturating arithmetic masks corrupt length words (`gc.rs:166`);
  `poly_word_to_bigint` reads `n_words*8` from a pointer trusting the length word with
  no cap (`rts.rs:1849`); `poly_set_code_constant` unchecked 8-byte write offset
  (`:2531`); `read_real_word` derefs after only `is_data_ptr` (`:2781`) — all the
  "trust the length word / trusted-image" family; cheap `debug_assert`s would catch
  codegen regressions.
- `loader.rs:370` silently drops code relocations (`let _ = relocs`, "Phase 2.2") —
  error if `!relocs.is_empty()` so a native-arch image fails loudly, not silently wrong.
- Stale: `rts.rs:344` "implementations can be filled in later" (real-math is done now);
  pexport two-pass dead code (`pass2_start`); module-scope `#![allow(dead_code)]` in gc.rs.

---

## SYNTHESIS — prioritized for release

**The one cross-cutting decision: state a threat model.** Three of four reviewers
independently land on the same line — the runtime is memory-safe on *trusted*
(Poly/ML-produced) images but **not on malformed/untrusted ones** (~30 handlers +
GC + RTS trust offsets/length-words from image data). For a v0.1 share the pragmatic
posture is **"trusted images only"**: one short README threat-model paragraph, fix the
cheap *reachable-from-bad-input* panics so accidental corruption degrades gracefully,
and add a `cargo-fuzz` target on `Image::parse`. Full untrusted-image hardening is a
larger, separable effort.

### Genuine bugs (fix regardless of threat model)
1. **JUMP32 sign-extension** (`interpreter/mod.rs:2908`) — zero-extends a 32-bit jump
   offset; upstream sign-extends → backward long jumps broken. Latent (no workload
   >64 KB hits it; oracle missed it). **1-line fix.** Highest-value correctness find.
2. **GC untracked-pointer use-after-free** (`gc.rs`) — gated but real; make it a hard
   error at minimum.

### Cheap robustness wins (bank before sharing)
3. pexport allocation bounds: `with_capacity(n)` (×2) + `vec![None; n_objects]` +
   `parse_entry_point` `checked_add` — the "tiny file → multi-GB OOM" DoS class.
4. `allocate()` / hot RTS allocators → `try_alloc` instead of `panic!` on exhaustion.
5. Handler-frame indexing guards (DELETE_HANDLER/RAISE_EX); `poly_shift_left` cap.
6. `read_u64`/`read_i64` `unwrap` → non-panicking; `--scan-isolated` `to_str().unwrap()`.

### Doc accuracy (cheap, matters for a shareable repo)
7. Stale comments that contradict code: CLI "work in progress" / "execution not
   implemented", `CALL_FAST_RTS` "stubbed", `GET_THREAD_ID` TODO, `real_to_int_round`
   doc, `rts.rs:344`, JIT install-count breadcrumbs, pexport two-pass dead code.
8. JIT: one consolidated "exception & overflow fidelity" section (FIXED_ADD wraps,
   FIXED_QUOT/REM trap, WORD_DIV/MOD return 0, RAISE_EX/SET_HANDLER stub).

### JIT (off-by-default; lower priority)
9. FIXED_QUOT/REM guard /0 (trap → abort); differential.rs false-divergence on
   interp-error; `install_all_jit_entries` → `unsafe fn`; `.expect()` → graceful error.

**Verdict:** no findings block a *preview* share once the threat model is stated.
The genuine-bug list (1-2) and the cheap-robustness list (3-6) are a focused,
~half-day batch that materially raises the floor. Nothing here undermines the
validated faithfulness on trusted images.

## polyml-jit (off-by-default testbed — findings weighted accordingly)

No BLOCKER. The translation arms spot-checked vs the interpreter (CONST_INT_B
zero-extend, binop pop-order, TAIL_B_B pop order, CASE16 range-guard, LOCK/CLEAR
masks, WORD/FIXED_MULT untag) are **correct and faithful**.

**SHOULD-FIX**
- **FIXED_QUOT/FIXED_REM emit bare `sdiv`/`srem`** (`translate.rs:1507`) → *trap*
  (SIGFPE/abort) on a zero divisor (and INT_MIN/-1), where the interpreter raises a
  recoverable `DivByZero`. A trap in JIT'd code aborts the host — strictly worse than
  the interp and worse than the WORD_DIV arm (which guards 0). Guard the divisor.
- WORD_DIV/WORD_MOD silently return tagged(0) on div-by-zero (`:430`) where the
  interp raises — an unmarked *value* divergence in an installed opcode.
- Install filter uses raw `bc.contains(&byte)` (`lib.rs:206`) — matches immediate
  bytes, not just opcodes (e.g. a `0x7b` jump offset reads as TAIL_B_B). Conservative
  (over-rejects → safe) but makes the install counts imprecise; use the opcode-aware
  walker (as `has_real_case16` already does).
- `differential.rs:159`: when the interp errors, the JIT is skipped and `jit_result`
  is left 0, then reported as a "divergence" — a false positive. Use `Option` for "JIT skipped".

**NICE-TO-HAVE**
- `.expect()` on `block_at` lookups (`translate.rs:1187`+, ~9 sites) panics if pass-1
  and pass-2 disagree on a target PC; since `compile_*` runs inside
  `install_all_jit_entries` (no catch_unwind) that aborts the host. `ok_or(TranslateError)`
  degrades gracefully.
- `install_all_jit_entries` has a `# Safety` section but is a normal `pub fn` doing
  internal raw-pointer walking — make it `unsafe fn` or rename to `# Preconditions`.
- ALLOC_WORD_MEMORY init loop uses a signed compare on the untagged length; stale
  install-count breadcrumbs in comments; blanket `#![allow(missing_safety_doc)]` now
  mostly unnecessary; consider gating `pub mod differential` behind a feature.
- OBSERVATION (strong): the **exception/overflow-fidelity gap is systemic** —
  FIXED_ADD wraps, FIXED_QUOT/REM trap, WORD_DIV/MOD return 0, RAISE_EX/SET_HANDLER/
  LDEXC stub. Each is commented locally; a single "Exception & overflow fidelity"
  section in the crate header listing all of them would make the boundary auditable.
  *The most valuable doc improvement for the JIT.*

---

## Resolution log — 2026-06-16

The genuine-bug + cheap-robustness batch (poly-free, verified by background
build + clippy + fmt + lib tests; the Euler proving fleet ran undisturbed).

**Banked**
- `7aafb4b` — **JUMP32 sign-extension** (genuine faithfulness bug): the three
  32-bit jump arms zero-extended their offset, so backward long jumps (functions
  >64 KB) jumped ~4 GB forward. Now cast through `i32`, matching upstream
  bytecode.cpp:2236. The 1300-case differential oracle never exercised it — no
  workload has a function that large. *Validated-against-an-oracle means
  validated on what the oracle exercised, not "correct."*
- `7aafb4b` — **GC untracked-pointer use-after-free**: an unforwarded from-space
  slot was logged then left dangling when `replace_storage` drops from-space.
  Now a hard panic (the set is always empty in correct operation; crash loudly
  on a collector bug rather than corrupt the heap).
- `9607e4c` — **pexport allocation amplification** (untrusted-image DoS): the
  reader pre-allocated from header counts before consuming input, so a ~20-byte
  malformed file could force a multi-GB OOM. `with_capacity` now bounded by
  remaining input; object table validates `n_objects` ≤ remaining bytes;
  `parse_entry_point` uses `checked_add`.
- `7f0db02` — GC roots log gated behind `POLYML_GC_QUIET`; pexport
  `read_u64`/`read_i64` `from_utf8().unwrap()` → propagated `BadNumber` (the
  parser is now fully panic-free on arbitrary input).

**Deferred (with rationale — not silent drops)**
- *DELETE_HANDLER bounds guard* — indexing is already Rust bounds-checked (safe
  panic on a malformed image, not UB); it's a hot opcode, so a redundant check
  isn't worth the cost. The threat model is memory-safety, which holds.
- *LargeWord over-shift (≥64)* — a faithfulness question vs upstream's
  shift-≥-wordsize semantics; needs an oracle diff to settle. Changing it blind
  risks introducing a divergence.
- *allocate→try_alloc retry* — the foundation audit already deferred this as a
  heap-corruption hazard (a pointer is cached across the allocation).
- *JIT NICE-TO-HAVE items* (exception/overflow fidelity header, `.expect()` →
  graceful degrade, install-filter precision) — JIT is a correctness testbed,
  not on the release-critical path; a separate pass.

**Verdict unchanged**: no preview-blockers under a stated "trusted images" threat
model; the untrusted-image amplification class (the one concrete BLOCKER three of
four reviewers converged on) is now closed on the parser side.
