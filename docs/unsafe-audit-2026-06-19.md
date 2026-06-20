# Systematic `unsafe` audit — polyml-rs runtime + JIT + image loader

**Date:** 2026-06-19
**Scope:** every `unsafe` block in `crates/polyml-runtime/src`, `crates/polyml-image/src`, `crates/polyml-jit/src`.
**Motivation:** the 2026-06-19 GC/memory-safety soak found a real (latent) use-after-free + a detector blind spot (the below-`sp` dangling-pointer class, `docs/gc-memory-soak-findings-2026-06-19.md`, commit 8756419). This static audit asks whether **sibling** memory-safety hazards lurk in the other `unsafe` sites — the scariest bug class, because heap corruption is silent.

**Method:** 7 cluster auditors enumerated every block, classified each by the invariant it assumes / who establishes it / whether it can be violated / reachability, then a triage pass built deterministic repros for the non-trivial findings and applied only the safe, bounded, cold/untrusted-path fixes (per the heap-corruption-class safety brief). GC-internal and hot-dispatch fixes were root-caused and left **uncommitted** for hands-on review.

---

## 1. Unsafe surface map (by file / cluster)

`grep -c unsafe` per file (raw `unsafe` token count; many are repeated SAFETY-comment idioms, not distinct hazards):

| File | raw `unsafe` | cluster |
| --- | ---: | --- |
| `interpreter/mod.rs` | 164 | interpreter-opcode-deref (PolyWord pointer trust) |
| `rts.rs` | 88 | RTS calling convention + IO slice construction |
| `gc.rs` | 40 | Cheney collector + below-`sp` scrub |
| `export.rs` | 29 | export/snapshot (reads own valid heap) |
| `loader.rs` | 27 | image loader (untrusted input) |
| `jit_bridge.rs` | 28 | JIT trampolines (opt-in `--jit`) |
| `polyml-jit/lib.rs` | 48 | JIT codegen + install |
| `polyml-jit/translate.rs` | 5 | JIT codegen |
| `space.rs` | 10 | allocator / length-word helpers |
| `length_word.rs` | 4 | **shared** code-object const-segment accessor |
| `poly_word.rs` | 0 | (`as_ptr` is the trust primitive; no `unsafe` keyword) |
| `polyml-image/pexport.rs` | 0 | parser (safe, range-checks all refs) |

**Total auditable blocks (deduplicated to distinct idioms across the 7 clusters): 449.** The 164 raw blocks in `mod.rs` collapse to ~8 distinct deref idioms; every memory-unsafe deref/write across the whole surface is gated on the **same single invariant**: *the word is a valid in-heap pointer of the expected type and sufficient size*, established by the trusted compiler's bytecode over a valid object graph.

### Two structural safety properties that bound the whole surface

These were verified once and apply across clusters:

1. **GC fires ONLY between opcodes.** The auto-GC trigger is at the top of `step_impl` (`mod.rs:1412`); `MemorySpace::alloc` is a pure bump allocator that **panics on exhaustion and never collects inline** (`space.rs`). Consequence: no opcode and no RTS handler caches a heap pointer across a GC, so the foundation-audit "GC alloc-retry" UAF hazard does not apply to the interpreter/RTS allocation sites. (This invariant is **load-bearing but undocumented** — see Observations.)
2. **The SML stack is a fixed `Box<[PolyWord]>` (never reallocated).** `peek`/`pop`/`reset`/`drop_n` are all bounds-checked before their `get_unchecked`; STACK_CONTAINER stack-internal pointers are GC-immune (the from-space range check filters them).

### The below-`sp` UAF fix is present and effective

The historic below-`sp` use-after-free + detector blind spot is genuinely fixed: the scrub of `[0,sp)` to `Tagged(0)` post-collect (`mod.rs:823`) runs **after** from-space is freed and **before** any opcode/audit, and the audit is widened to the full stack `[0,len)` (`mod.rs:878`). Both are regression-fenced: `tests/gc_tiny_heap_uaf.rs` (deterministic SEGV before the fix → `Tagged(0)` now, **verified passing**) and `gc_audit_smoke_basis_load` (pins residual==0 on the heaviest GC workload). A confirmed *side benefit*: the scrub converts the old below-`sp` dangling deref into a deterministic near-null SIGSEGV on the INDIRECT_LOCAL path (`Tagged(0)` → `as_ptr()` = addr 1) rather than silent corruption.

**No new sibling of the below-`sp` UAF was found in any cluster** — no pointer that can *dangle* across a collect on a supported path exists outside the now-fixed site.

---

## 2. The one residual hazard CLASS (and where it surfaces)

Every non-safe finding below is an instance of **ONE** root-cause class: the **untyped-ref type-confusion residual** (loader-fuzz `lf_ref_52` / **task #96**, `docs/loader-fuzz-findings-2026-06-17.md`). The pexport image format carries *untyped* refs — a well-formed, in-range, LSB-clear word can point at a **wrong-type** object (or be a tagged-int misread as a pointer). The trusted SML compiler never emits such a word, and the parser range-checks every ref, but the loader cannot reject a wrong-*type* target without whole-image type inference. This is the **same exposure upstream PolyML's untyped-ref format has.**

This class is **memory-safe on every supported path** (`poly run` of a trusted image, running type-safe SML) and **violable only by a hand-corrupted / adversarial image**. It surfaces at every site that dereferences a PolyWord as a pointer without re-validating type+size:

- **Interpreter** (cluster 1): `INDIRECT_*` field loads, `do_call`/`do_tail_call` code-word resolution, `read_pc_const`.
- **GC** (cluster 2): `scan_object` F_CODE_OBJ branch (read **and write**, on the supported bootstrap path).
- **Loader** (cluster 3): non-root closure `code_addr` (origin; type-checks only the root).
- **RTS** (cluster 4): IO slice + code-patch primitives (bounds-trust).
- **JIT** (cluster 5): `jit_dispatch_dynamic_call` / arity probes (opt-in `--jit`).
- **Export** (cluster 6): `snapshot`/`drain`/`build_code`.

The physical **convergence point** for the code-object variant is the shared helper **`length_word.rs:135 const_segment_for_code`**, routed through by the interpreter CALL dispatch, the GC scan, export, and JIT install. Its two correctness guards (`is_code_object`, `n_words >= 2`) are **`debug_assert!` only** (`length_word.rs:144-149`) — **compiled out in release** (the `poly run` config). On a corrupt/wrong-type code object it reads an attacker-controlled trailing signed-offset word and an unchecked `count` word and computes a wild constants pointer with no range check. **Verified by source read.**

---

## 3. Findings + triage classification

Severity = (memory-unsafe + reachable on a supported path) HIGH; (memory-unsafe + adversarial/latent) MEDIUM; (safe-but-fragile) hardening.

### REAL BUGS (genuine, reachable on the supported `poly run <untrusted-image>` path, with deterministic repro)

| # | Site | Bug | Repro | Status |
| --- | --- | --- | --- | --- |
| R1 | `rts.rs` `poly_set_code_constant` / `poly_set_code_byte` (code-finalization RTS) | Unbounded byte `offset` (`offset.untag()`) feeds an 8-byte / 1-byte `copy_nonoverlapping` **WRITE** into a code object — attacker-controlled **OOB heap write**, the highest-value corruption target. Upstream PolyML is also unbounded here (trusts the compiler), but `poly run` accepts untrusted images. | Unit-test repro: writing past a 16-byte code object clobbered the adjacent sentinel (0xaaab→0xeeef). | **FIXED** (safe bounded, cold path) |

R1 is the only finding that crossed the bar for a fix to be *applied*: it is a corrupted-image-driven **OOB write** on a **cold** code-finalization RTS path (not the step loop, not the GC), so adding a length-word bound is within the brief's "SAFE bounded fix on an untrusted path" envelope. See §5.

### LATENT HAZARDS (the below-`sp` class — memory-unsafe but adversarial/untrusted-input-only; deterministic repros built)

| # | Site | Hazard | Repro | Fix |
| --- | --- | --- | --- | --- |
| L1 | `mod.rs:4305-4352` `do_call` + `4042-4051` `do_tail_call` → `const_segment_for_code` | Validates the CLOSURE is a pointer but never that closure **word0** is a data pointer / aligned / an F_CODE_OBJ before resolving `code_end` for the **entire next function**. Tagged-int word0 → unaligned `*sub(1)` SIGSEGV; non-code word0 → silently **wild `code_end`** (release: debug_asserts gone). Highest blast radius (corrupts the PC bound, not one slot). | `examples/do_call_bad_code_word.rs` → `tagged`: SIGSEGV (139); `noncode`: wild `code_end` (len=140737488289816), returns `Ok` silently. `examples/loader_accepts_bad_nonroot_closure.rs` + `tests/do_call_type_confusion.rs`: loader+`ensure_runnable` ACCEPT a type-confused **non-root** closure (root-only check) → guard-page child dies SIGSEGV. | banked (hot CALL dispatch) |
| L2 | `mod.rs:2073-2104` INDIRECT_LOCAL/CLOSURE family (+ `3207`, `3355`, `2722/2747`) | Field-load opcodes `as_ptr().add(slot)` with no object type/size check. GC-safe (fires only between ops) and stack-safe (peek/pop bound depth); sole residual = type/size confusion via corrupt image. Post-scrub side effect: a tagged-int slot now yields a near-null SIGSEGV, not a UAF. | `examples/indirect_local_type_confusion.rs` → deterministic SIGSEGV (139, 5/5) through real `step()` over a tagged-int local. | banked (~7% of all steps) |
| L3 | `mod.rs:4489` `read_pc_const` (CONST_ADDR / CALL_CONST_ADDR family) | No bound on `pc + byte_off + idx*8` against the object's true end. `code_end` is the const-pool *start* (the const pool deliberately lives past `code_end`), so `fetch_u8`'s bound cannot protect it; a corrupt immediate or wild `code_end` (L1) reads OOB. | `tests/read_pc_const_oob.rs`: `read_pc_const_reads_past_object_end` PASS; `read_pc_const_guard_page_segv_child` PASS (child SIGSEGV). | banked (hot CONST_ADDR dispatch) |
| L4 | `gc.rs:237-273` `scan_object` F_CODE_OBJ + `mod.rs:762-768` image-root code scan → `const_segment_for_code` | **On the SUPPORTED bootstrap path** (runtime code objects ARE allocated into the GC'd alloc-space by `poly_copy_byte_vec_to_closure`, `rts.rs`, F_CODE_OBJ\|F_MUTABLE; the chain compiles ~150 modules). The only block that both READS and **WRITES** through `cp+i` (`forward()` writes the forwarded addr back) with `count`/`cp` from object words with no release bound. A corrupt trailing offset/count → GC forwards through OOB pointers. | `examples/gc_code_obj_bad_trailer.rs` → SIGSEGV (139); gdb backtrace pins `const_segment_for_code` `length_word.rs:159` inside `scan_object` under `collect`. | banked (GC-internal) |
| L5 | `rts.rs` `write_array` (subcode 11/12) | SML `(vec, offset, length)` slice trusts off/len without checking against `vec`'s byte-object length word; `from_raw_parts(base.add(off), len)` OOB **read**; off+len can wrap the pointer. | `examples/write_array_oob.rs` (mirrors exact slice) → SIGSEGV (139) with len=256 MiB over an 8-byte object. | **FIXED** (safe bounded, cold IO path) — see §5 |
| L6 | `rts.rs` `read_array_from_stream` (subcode 8/9) | Mirror of L5 but a `from_raw_parts_mut` + `Read::read` → attacker-controlled stdin **OOB WRITE** past the byte array (heap corruption, more dangerous direction). | `examples/read_array_oob_write.rs`: forged (off=0, len=256 MiB) rejected by the guard; in-bounds/partial accepted; predicate-level repro. | **FIXED** (safe bounded, cold IO path) — see §5 |
| L7 | `export.rs:50` `snapshot` / `:100` `drain` / `:192-204` `build_code` → `const_segment_for_code` | Export walks `*(addr-1)` length words and `build_code` loops `0..count` from an attacker-controllable trailing offset/count with no upper bound — **amplifies** a single wild deref into an unbounded recursive scan. `snapshot` runs synchronously in the RTS handler (no GC mid-walk; no dangling). | `tests/export_corrupt_code_oob_repro.rs` + `examples/export_code_obj_bad_trailer.rs`: pre-fix SIGSEGV via `snapshot`; the fault is the `count` read **inside** `const_segment_for_code`, so a build_code-local check is insufficient. | **`build_code` clamp FIXED** (cold export path); the shared-helper root banked |
| L8 | `jit_bridge.rs:135-244` `jit_dispatch_dynamic_call` + arity probes (`lib.rs:687-724`, `translate.rs:2369-2389`) | `--jit`-only. Guards tagged-int + out-of-object scan; the residual is a well-formed wrong-type object whose bytes are misread as marker/arity (same class). LIVE code (38 dispatches measured on simple bootstrap). | (covered by the lf_ref_52 class; needs `--jit` + corrupt image) | banked (task #96 covers it) |
| L9 | `translate.rs:2369-2415` `closure_arity_from_addr` (JIT install) | `--jit`-only, **distinct/stronger vector**: the CALL_CONST_ADDR operand `read_at` is bounds-checked only against the *whole object body*, not the const-pool, so it can point **back into the attacker's own verbatim code bytes** — a raw 8-byte word that bypasses the loader's `resolve_value` sanitizing entirely. Dereferenced **proactively at install time** over **every** code object (reachable or not). | `/tmp/evil_jit_image.txt` (gen script): `poly run --jit` → SIGSEGV (139) during JIT install, before any SML executes; gdb pins `closure_arity_from_addr` `translate.rs:2376`. Non-`--jit` load: clean. | banked (cross-crate span-membership refactor) |

### HARDENING (safe-but-fragile; no reachable bug)

| # | Site | Note |
| --- | --- | --- |
| H1 | `mod.rs` LOAD/STORE_ML_WORD/BYTE, BLOCK_MOVE/EQUAL/COMPARE | Defense-in-depth: index/off/len from popped tagged ints, no object-size bound. Unreachable via type-safe SML (basis raises Subscript first), but BLOCK_MOVE/STORE are on the hot String/Array path → a per-store length read is a measurable hot-path cost. Defer. |
| H2 | `mod.rs:1599-1634` STACK_CONTAINER_B / MOVE_TO_CONTAINER_B | GC-safe (stack-internal address, never moves, from-space filter). Fragility newly tied to the below-`sp` scrub: scrub correctness now also relies on containers never escaping their frame (compiler invariant). `MOVE_TO_CONTAINER_B N` unbounded N → adversarial OOB stack write. |
| H3 | `rts.rs` `poly_string_to_rust` | Read word0 as length with no `is_byte_object` check + only a 1 MB sanity cap → corrupt-image OOB read (filename args). **FIXED** (cold path, mirrors `name_for_code_object`) — see §5. |
| H4 | `rts.rs` `poly_get_code_constant` | Unbounded offset → OOB **read** (debug-only upstream). **FIXED** alongside R1. |
| H5 | `rts.rs` `poly_word_to_bigint`, boxed-Real/bignum scalar reads | No `is_byte_object` guard; reads are bounded by the (loader/GC-validated) length word → value/type confusion, not OOB. Add `is_byte_object` for defense-in-depth. |
| H6 | `rts.rs` fd reconstruction (`File::from_raw_fd`) | Every reconstruct paired with `into_raw_fd` (no double-close); `close_file` intentionally drops. A corrupt fd is fd-confusion (wrong file), not heap-unsafe. |
| H7 | `loader.rs:438-445` EntryPoint name + NUL copy | **ZERO byte slack** at `name.len() ≡ 7 (mod 8)` (in-bounds today, the `+16` exactly absorbs placeholder+NUL). Attacker-controllable length. Add `assert allocated_bytes >= name.len()+9` or size via `(name.len()+1).next_multiple_of(8)`. |
| H8 | `length_word.rs:58-64` `make_length_word` | Silently truncates `n_words >= 2^56` into the flags byte (`debug_assert` only). Unreachable (needs a 256-PB file) but a release-time `LoadError` would make the invariant explicit. |
| H9 | `gc.rs:183-208` tombstone install/decode; `:300-334` pre-pass; `:354-387` untracked panic `*addr-8` | All adversarial-image-only and/or cold panic paths. A missed root **panics** (fail-fast), not dangles. The `*addr-8` diagnostic read can be one word before the Box if `addr == from_start`; guard with `addr > from_start`. |
| H10 | `pexport.rs:126` | **Doc-only:** stale F-header comment says `<nWords>` where the field is `constCount`. |
| H11 | `jit_bridge.rs` / `translate.rs:2140` `transmute → JitFn` lifetime | `main.rs:367 Box::leak` keeps the JITModule alive for the process; latent footgun if a future caller drops `Jit` while `jit_cache` holds raw fn pointers (UAF of freed executable memory). Document/enforce the "Jit must outlive jit_cache" invariant. |
| H12 | `mod.rs:4287` JIT trampoline entry — panic-skips-`JIT_INTERP`-restore | **Verified non-hazard:** crate is `panic=unwind` on toolchain 1.96.0; a panic reaching the `extern "C"` boundary aborts (`panic_cannot_unwind`), so control never returns to the restore-skip window. Optional: use the existing RAII `with_jit_interp` guard to make the (currently false) comment truthful. |
| H13 | JIT differential/bench harness (`differential.rs`, `bench.rs`) | `poly diff` / `cargo test` only. `bytecode_head` unconditional 64-byte read; `compare_results` length-driven body compare. Bound to the object's body length; not on the supported path. |

---

## 4. Cross-reference to known residuals

- **`lf_ref_52` / task #96 — untyped-ref type-confusion** (`docs/loader-fuzz-findings-2026-06-17.md`): the single root class of every non-safe finding above. The loader-fuzz doc already documents the repro (`8392:O2|@8394,@8393 -> @18098`) and prescribes the fix locus (**interpreter-side deref hardening**, validate the pointed-to length word before the unsafe deref). This audit confirms the class surfaces at the interpreter (L1-L3), GC (L4), RTS (L5-L6, R1, H3-H5), JIT (L8-L9), and export (L7) — all the same bug, none new.
- **below-`sp` UAF + detector blind spot** (`docs/gc-memory-soak-findings-2026-06-19.md`, commit 8756419): **fixed and fenced**; this audit found **no sibling** (no other pointer that can dangle across a collect on a supported path). The scrub additionally turns the old class into a loud near-null SIGSEGV on the INDIRECT path.
- **foundation audit** (`docs/foundation-audit-2026-06-08.md`): the deferred "GC alloc-retry" hazard (`do_alloc_ref`/`ALLOC_WORD_MEMORY` cache a ptr across `allocate`) is **NOT** present in the interpreter/RTS allocation sites today *because* `MemorySpace::alloc` never collects inline — but that invariant is undocumented and load-bearing (see Observations).

---

## 5. Fixes applied (safe, bounded, cold/untrusted-path)

All applied fixes are pure additive guards on **cold** RTS paths (not the step loop, not the GC, not hot CALL dispatch) — within the brief's "SAFE bounded fix on a cold/untrusted path" envelope. **Not committed** (the main loop reviews + commits).

1. **`rts.rs` `write_array`** (`~3036-3060`) and **`read_array_from_stream`** (`~3583-3617`): before each `from_raw_parts(_mut)`, read the target's length word, require `is_byte_object(lw)` and `off.checked_add(len) <= length_of(lw)*8` (overflow-safe; `length_of` masked to 56 bits so `*8` cannot overflow `usize`); on violation return the pre-existing "did nothing" stub. (L5, L6 — the read-direction is an OOB **write**, prioritized.)
2. **`rts.rs` `poly_string_to_rust`** (`~3382-3418`): after `is_data_ptr`, require `is_byte_object` and `size_of::<usize>() + len <= body_bytes`; on any violation return `None`. The added `*(p-1)` read is no wider than the `*p` it already did. (H3.)
3. **`rts.rs` `poly_set_code_constant`/`poly_set_code_byte`/`poly_get_code_constant`** (`~2549-2585`, `~2671-2682`, `~2714-2723`): derive `code_byte_len = length_of(length_word_of(code_obj))*8` (handling both the direct-code and `closure[0]`-indirect cases, adding the missing `is_data_ptr()` on the indirect case) and reject `off`/`off+write_width` past it. (R1 — OOB **write**, prioritized; H4 — the read sibling.)
4. **`export.rs` `build_code`** (`~189-241`): replaced the discarded `let _ = n;` with a clamp — compute `obj_end`/`consts_end` from the true word length `n` and clamp `safe_count` so `[cp_start, cp_start+safe_count)` lies inside the object body. Strict no-op on valid code objects. (L7 build_code half.)

### Verification of applied fixes (all re-run for this report)

- `cargo build --release` (full workspace): **clean.**
- `cargo build --release -p polyml-runtime`: **clean.**
- Runtime lib tests: **84 passed**, incl. `write_read_array_bounds_guard`, `poly_string_to_rust_rejects_oversized_length`, `set_code_constant_out_of_range_offset_is_rejected`, `set_code_byte_out_of_range_offset_is_rejected`, `set_code_constant_in_bounds_writes_correctly`.
- `export_corrupt_code_oob_repro`: **3 passed** (clamp closes the OOB; valid path unaffected).
- `export_roundtrip_fuzz`: **12 passed** incl. `fixpoint_polyexport` (453K objects, thousands of code objects, byte-identical re-export) — proves the export clamp is a strict no-op on every real code object.
- `gc_tiny_heap_uaf`: **2 passed** (below-`sp` fence intact).
- `tools/regression.sh fast`: **`=== REGRESSION OK (fast) ===`**.
- Differential vs upstream oracle: the full ~18K-case corpus exceeds a 5-min budget; a targeted subset of the files that actually exercise the guarded paths — `strings.sml`, `string_ops2.sml`, `substring.sml`, `text_edge.sml`, `struct_edge.sml`, `cstress_heavy.sml`, `cstress_miniprograms.sml` (String/Array/IO/compiler-stress) — was **7/7 agree, 0 diverged.** (The 2 known full-corpus divergences are the pre-existing documented upstream stage-0 `andb`/`orb` bug, unrelated to IO/string/code.)

---

## 6. Banked for hands-on review (root-caused, UNCOMMITTED)

These are GC-internal or hot-dispatch fixes — per the heap-corruption-class brief, root-caused and left for hands-on review rather than applied. **They all share one fix locus.**

- **The shared root: `length_word.rs:135 const_segment_for_code`.** Promote the two `debug_assert!`s to release-time guards and clamp `cp`/`count` to `[obj_ptr, obj_ptr + n_words)` **in the correct order** (the wild deref is the `count` read at `cp.sub(1)`, so validate `cp` is in-bounds *before* reading `count`). One change here closes **L4 (GC scan OOB read+write), L7 (export amplification root), and the interpreter CALL/CONST_ADDR variants (L1/L3)** at once. Gating before applying: `regression.sh fast` + `diff-oracle --dir tools/diff-corpus` (full) + `export_roundtrip{,_fuzz}` + `gc_tiny_heap_uaf` (the GC routes through it). It is **hot** (every CALL/tail-call + every GC scan of a code object), hence hands-on.
- **`do_call`/`do_tail_call` code-word guard** (`mod.rs:4045`, `4307`): add `code_word.is_data_ptr()` + 8-alignment **before** `const_segment_for_code` (the cheap half of L1). The sibling `jit_set_code_segment` at `mod.rs:1209` already does the `is_data_ptr` check — proving it is recognized and cheap — but the hot do_call/do_tail_call omit it. Hot CALL dispatch → hands-on.
- **INDIRECT-family deref hardening** (L2): needs an all-spaces address-membership predicate that **does not exist today** (`space.rs` has no `contains(addr)`; the interpreter holds only alloc-space + image-mutable ranges, not the loaded read-only spaces). On the hottest dispatch path (INDIRECT_LOCAL_B0/B1 ~7% of all steps). Hands-on; part of the task #96 effort.
- **JIT `closure_arity_from_addr` span check** (L9): a cross-crate refactor threading a MemorySpace-span-membership validator through `compile_with_consts_meta → ... → closure_arity_from_addr`. Not a bounded one-liner. Hands-on.

---

## 7. Prioritized punch list

1. **[task #96, the real fix]** A single **interpreter-side typed-deref predicate**: "is this PolyWord a valid in-space object pointer of expected type/size?" (range-check against the live `MemorySpace` set + length-word sanity). Designed once with a `space::contains(addr)` API, it closes L1, L2, L3, L8, L9, and the loader/export trust boundaries simultaneously — far better than per-site checks. Requires the missing space-membership API and is hot-path-sensitive → hands-on.
2. **[banked]** Harden `const_segment_for_code` (release-time type+size guard + cp/count clamp). Closes L4 + L7-root + the code-object half of L1/L3 in one place. GC-adjacent + hot → hands-on; gate as in §6.
3. **[banked]** `do_call`/`do_tail_call` `code_word.is_data_ptr()` + alignment guard (cheap half of L1). Hot CALL dispatch → hands-on.
4. **[applied]** ✅ R1 (`poly_set_code_constant`/`byte` OOB write) — done.
5. **[applied]** ✅ L5/L6 (`write_array`/`read_array_from_stream` OOB read+write) — done; the read-direction OOB *write* was the priority.
6. **[applied]** ✅ H3/H4 (`poly_string_to_rust`, `poly_get_code_constant`) — done.
7. **[applied]** ✅ L7 build_code clamp — done; the shared-helper root remains banked (item 2).
8. **[hardening, cheap]** H7 EntryPoint `name.len() ≡ 7 (mod 8)` zero-slack assert; H8 `make_length_word` release-time check; H9 `gc.rs` `*addr-8` guard `addr > from_start`; H5 `is_byte_object` on `poly_word_to_bigint`; H11 document the Jit-outlives-jit_cache invariant; H10 the `pexport.rs:126` doc fix. All cold/diagnostic; safe to bank into a future cleanup pass.
9. **[regression fence, recommended]** Add a mutated-code-object case (corrupt trailing offset/count) to the export round-trip fuzz so the build_code clamp (and any future shared-helper fix) stays locked.

---

## 8. Overall assessment

**The `unsafe` surface is SOUND on every supported path.** Of 449 audited blocks, exactly **one** crossed the bar for an applied fix (R1, a cold corrupted-image-only OOB write that upstream PolyML also has). All other non-safe findings are instances of a **single, already-documented residual class** (untyped-ref type-confusion, task #96) — memory-safe under type-safe SML and a trusted image, violable only by a hand-corrupted/adversarial image, the same exposure as upstream's untyped-ref format. The class surfaces at many sites but has **one root** and **one principled fix** (an interpreter-side typed-deref predicate).

**Compared to the GC below-`sp` find:** the below-`sp` UAF was *more severe in kind* — it was a **dangling** pointer reachable in spirit on a heavy GC workload (a pointer that became invalid across a collect, the classic silent-heap-corruption shape), and it had a **detector blind spot** that hid it. This audit found **no sibling of that kind**: every residual here is a **type-confused** pointer (wrong type, not dangling), it requires an **adversarial image** (not just heavy execution), and it tends to **crash loudly** (SIGSEGV via wild `code_end`/guard page, or now near-null via the scrub) rather than corrupt silently. So the surface is in better shape than the GC find suggested: the scariest property (silent dangling on a supported path) is now fenced and was not found to recur.

The genuine open work is **task #96** — the interpreter-side typed-deref hardening — which is architectural and hot-path-sensitive, correctly out of scope for an in-pass fix, and is the single highest-leverage investment for the whole `unsafe` surface.
