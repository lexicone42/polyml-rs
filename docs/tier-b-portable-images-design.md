# Tier B — portable cross-arch heap images (design / scope)

*2026-06-16. Scoping pass for the headline release goal: the original*
*"RuPaulyML … portable (across arches etc) heap images" vision.*

## TL;DR — we are much closer than "port a format from scratch"

Two facts, both verified against the code below, collapse most of the work:

1. **Our image format is already architecture- and word-size-neutral on the
   wire.** It's the upstream PolyML *portable export* text format ("pexport" =
   *portable* export): decimal integers + hex byte strings, inter-object
   pointers stored as **object IDs** (not addresses), entry points stored **by
   name**. Nothing in the serialized bytes assumes a word size or an endianness
   (`crates/polyml-image/src/pexport.rs`).

2. **We are an interpreter — all our images are bytecode, never native code.**
   `export::snapshot` only ever writes `SourceArch::Interpreted` /
   `WordSize::Bits64` (`export.rs:56-57`). The single genuinely
   non-portable thing in upstream's format — relocating **native machine code**
   across architectures — *does not apply to us*. Bytecode is the same bytes on
   x86_64 and aarch64.

The consequence: **x86_64 → aarch64 (both 64-bit little-endian) needs no format
change at all.** The bytecode is identical, pointers are object IDs resolved at
load, RTS calls are re-linked by name, and `size_of::<usize>()` is 8 on both
hosts. What's missing is (a) *safety* — the loader silently trusts that the
image's word size matches the host — and (b) an actual *demonstration* on a
second architecture. That's the MVP.

The harder, genuinely-format-level work (cross **word size**, 64↔32) is a
*stretch* goal and arguably out of scope for the tweet (the "arches" people care
about — x86_64, aarch64 — are all 64-bit).

## What upstream's portable format gives us (and we already match)

`vendor/polyml/libpolyml/pexport.cpp` (David Matthews, "Export and import memory
in a portable format", 2006–2025) is explicitly cross-arch / cross-word-size by
design. Its mechanisms, and our status:

| Mechanism | Upstream | polyml-rs |
| --- | --- | --- |
| Inter-object pointers as object index `@N` | pexport.cpp:97-108 | `Value::Ref(id)`, two-pass resolve (`loader.rs:173-231`) ✅ |
| Tagged ints as decimal text | pexport.cpp:102-108 | `Value::Tagged(i64)` ✅ |
| Header records arch + word size | pexport.cpp:304-315 | `Root <id> <arch> <wordsize>` (`pexport.rs` header) ✅ written, ⚠️ ignored on load |
| Entry points by **name**, relinked on import | pexport.cpp:851-870 (`setEntryPoint`) | `patch_entry_points` re-looks-up by name every load (`loader.rs:255-275`) ✅ |
| Code objects as hex bytes + relocs | pexport.cpp:192-224 | `ObjectBody::Code { code_bytes, constants, relocs }`; relocs always empty (interpreted) ✅ for us |
| Native-code relocation across arch | pexport.cpp:806-828 (`SetConstantValue`) | **N/A** — we never emit native code |

Upstream's own documented caveat (pexport.cpp:167-180): across **different word
sizes**, arbitrary-precision integers can flip between tagged-short and
long-boxed representation, and the format "does NOT guarantee correctness without
recompilation." This is precisely the part we defer.

## Verified current state (the gaps)

**Gap 1 — the loader trusts the host word size, never the image's.**
Every object-size computation uses the compile-time `size_of::<usize>()`, not the
`word_size` parsed from the header:

- `loader.rs:89,92,100,106` — String/Bytes/Code/EntryPoint body word counts
- `loader.rs:328,360-361` — code-object layout + trailing offset word
- `loader.rs:409` — byte-packing padding

The header's `arch`/`word_size` are read **only** for the `poly info` printout
(`main.rs:619-620`), never to validate or adapt. So loading a 32-bit image on a
64-bit host (or vice-versa) silently misallocates every variable-length object →
heap corruption / SEGV. *Same* word size across arch is unaffected (8 == 8).

**Gap 2 — no cross-arch demonstration.** We have only ever built and run on
x86_64. There is no aarch64 build, no QEMU/`cross` harness, and no test that
moves an image between arches.

**Non-gap — endianness.** We are little-endian only (`PolyIsBigEndian` returns 0,
`rts.rs`), and both x86_64 and aarch64 are LE. Bytecode and tagged-int bit
patterns are endian-agnostic. No work needed for the target arches.

## Portability matrix (interpreted images)

| From → To | Status | Why |
| --- | --- | --- |
| x86_64 → aarch64 (64-bit LE) | **Works today, unsafe** | identical bytecode, object-ID pointers, by-name RTS; only missing a validation guard |
| x86_64 → x86_64 (different build) | Works | `patch_entry_points` relinks tokens by name (`[[rts-token-staleness]]` is the failure mode if names change) |
| 64-bit ↔ 32-bit | Broken (stretch) | loader sizes objects from host `size_of::<usize>()`, not image word size; plus the arbint tagged/long boundary |
| any → big-endian | Out of scope | runtime is LE-only by design |

## Proposed scope

### MVP (the headline: "portable across arches")

1. **Load-side validation + adaptation switch.** Thread the header
   `word_size`/`arch` into `load_image`. For the supported case (image word size
   == host word size), proceed. For a mismatch, return a clear
   `LoadError::WordSizeMismatch { image, host }` instead of silently corrupting
   the heap. This is small, safe, and turns "undefined behaviour on a wrong-arch
   image" into a clean error — worth doing regardless of the demo.
   *Files: `loader.rs` (plumb `image.word_size` in; the `body_word_count` and
   code-layout sites already centralize the arithmetic).*

2. **aarch64 build + run harness.** Stand up an aarch64 path: either
   `cross`/`cargo` with the `aarch64-unknown-linux-gnu` target run under
   `qemu-aarch64`, or a native runner if available. Confirm the workspace builds
   (the JIT crate is Cranelift — gate `--no-default-features`/feature-flag the
   JIT off for the interpreter-only aarch64 build if Cranelift cross is fiddly;
   the interpreter is the portability story, not the JIT).

3. **The cross-arch demo + test.** Produce `polyexport` on x86_64 (the existing
   self-bootstrap), then on aarch64 run `poly run polyexport` with the `fact 10`
   REPL line and assert `3628800`. Wire it as an `#[ignore]` integration test +
   a `tools/` script, fenced like the other heavy demos. This *is* the tweet:
   "a heap image our Rust runtime built on x86_64, executing on aarch64."

### Stretch (cross word size, 64↔32)

4. Size every object from the **image's** `word_size`, not the host's — convert
   `body_word_count` & the code-layout math to take a `word_bytes` parameter.
5. Handle the arbitrary-precision-integer tagged/long boundary on load (upstream
   pexport.cpp:167-180 caveat) — detect a long-form value that fits the host's
   tagged range (and vice-versa) and normalize. This is the subtle correctness
   piece; defer until 64↔32 is actually wanted.

## Risks / unknowns

- **Cranelift on aarch64.** Cranelift supports aarch64, but cross-building +
  running the JIT under QEMU may be slow/awkward. Mitigation: the portability
  claim is about the **interpreter**; build the aarch64 demo interpreter-only.
- **QEMU fidelity.** `qemu-user` is good enough for a correctness demo; a real
  aarch64 box (CI runner / cloud) would be a stronger artifact if available.
- **Latent host-width assumptions outside the loader.** The audit found the
  loader is the concentration point, but a sweep for stray `as u64` / `usize`
  punning in the interpreter's image-root scan is prudent before claiming 64↔32.
- **RTS token staleness across builds** (`[[rts-token-staleness]]`) is *already*
  handled by by-name relinking — but the two builds (x86_64 and aarch64) must
  register the same RTS entry-point **names** (they will: same `rts.rs`).

## Milestones

- [x] M1 — `LoadError::WordSizeMismatch`: plumb header word size into the loader,
      validate, clear error on mismatch (+ unit test). **DONE** (commit 76da2ec):
      simple bootstrap still loads clean; `rejects_cross_word_size_image` passes.
- [ ] M2 — aarch64 build green. *Prepped:* `cross` + docker + podman are
      installed (no native aarch64 target / qemu needed — `cross` containerises
      both). `poly` depends on `polyml-jit` unconditionally, so the build needs
      Cranelift to cross-compile — expected fine (Cranelift is pure Rust with
      runtime host-detection via `cranelift-native`). Fallback if it doesn't:
      feature-gate the JIT out of `polyml-bin` for an interpreter-only build.
      Run: `tools/cross-arch-demo.sh --build`. *Hold until Euler finishes to
      avoid CPU contention with the proof fleet.*
- [ ] M3 — x86_64-built image runs on aarch64 under qemu. **Harness written**
      (`tools/cross-arch-demo.sh`): M3a runs the checked-in `bootstrap64.txt`
      (proves load+exec on aarch64, always available); M3b runs `fact 10` →
      `3628800` through the self-bootstrapped `polyexport` if present (the REPL
      headline). Promote to an `#[ignore]` integration test once green.
- [ ] M4 (stretch) — object sizing from image word size; 32-bit image loads on
      64-bit host (round-trip test).
- [ ] M5 (stretch) — arbint tagged/long normalization across word sizes.

## Real-hardware path: Apple Silicon macOS

The qemu/`cross` route (M2/M3) is the CI-friendly demo, but a native **Apple
Silicon Mac** (arm64) is a stronger artifact: it exercises cross-arch **and**
cross-OS at once (x86_64-Linux-built bytecode → arm64-macOS) on real hardware,
no emulation. The macOS build is pre-vetted clean (2026-06-16): no Linux-isms
(only `#[cfg(unix)]` getrusage, which macOS satisfies), and the JIT is opt-in
behind `--jit` so a plain `poly run` never invokes Cranelift. Recipe:
`cargo build --release -p polyml-bin` (target `aarch64-apple-darwin`, native),
then `poly run bootstrap64.txt` (expect `Tagged(0)`) and `fact 10` through
`polyexport` (→ `3628800`). Gated on getting the repo onto GitHub + transferring
the (git-ignored) `vendor/` images. A test machine is available for this.

## Bottom line

The "portable across arches" headline is **M1 + M2 + M3** — a validation guard
plus an aarch64 build plus one demo — not a format port. Being an interpreter is
what makes this cheap: we never have native code to relocate, so the only thing
that crosses the arch boundary is bytecode + object-graph + names, all of which
the format already carries portably. The cross-*word-size* work (M4/M5) is real
format engineering and is correctly a stretch goal.
