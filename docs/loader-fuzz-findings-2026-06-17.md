# Loader robustness fuzz — findings (2026-06-17)

Mutation-fuzzed the heap-image loader (the untrusted-image threat model) via
ultracode wf_bc3b7334-e88: 6 mutation strategies (truncate / numeric / ref /
type / byteflip / header) over `vendor/polyml/bootstrap/bootstrap64.txt`, each
mutant fed to `poly run` (timeout 15, `--max-steps 5M`), classified by exit code.

**Threat model:** loading an untrusted image must never cause memory unsafety —
acceptable = clean error (exit 0/1/2) or controlled panic (101); UNACCEPTABLE =
SIGSEGV (139), SIGABRT (134), hang (124), OOM-kill (137).

## Result

500 mutants. The **DoS hardening held perfectly**: zero hangs, zero OOM-kills,
zero aborts, **zero panics** — the alloc-bounds caps, `checked_add`, panic-free
`read_u64/i64`, and word-size validation all degrade malformed bytes into clean
`ParseError`/`LoadError`. But **23 deterministic SIGSEGVs** surfaced, reducing to
**two HIGH memory-safety bugs** — *structural* invariants the loader never checked
but the interpreter's `unsafe` code assumes. **Both fixed (commit e472804)**;
589/590 kept mutants now exit cleanly.

| Bug | Repro | Fix |
|-----|-------|-----|
| **Non-closure / mis-pointed root** (22/23) | 28 bytes: `Objects 1\nRoot 0 I 8\n0:O1|0\n` — in-range root that isn't a closure-to-code | `load_image` records `LoadedImage.runnable` (root is a closure whose `code_addr` refs a code object); `main.rs::ensure_runnable` gates every run path before the unsafe `*root` code-pointer deref. Loader stays permissive (data-only images still load). |
| **Count/payload mismatch** | `O0|@a,@b` — 0-tuple with trailing refs silently dropped → under-sized object → read past it | `parse_object_line` requires the payload to consume the whole line (else `ParseError`). |

Regression tests: `loader::non_closure_root_is_not_runnable`,
`pexport::object_line_trailing_content_rejected`.

## Residual (open, task #96)

**`lf_ref_52`** — `8392:O2|@8394,@8393` → `@18098`: a 2-tuple field re-pointed to a
**valid but wrong-type** object (a code object). The ref is in-range and the line
is well-formed, so it's an **untyped-ref type confusion** that only manifests when
the interpreter *uses* the field — the loader can't catch it without whole-image
type inference. This is a limitation of the untyped-ref image format **shared with
upstream PolyML** (loading a hand-corrupted image into real PolyML can crash too).
Fully closing it needs **interpreter-side deref hardening** (the field-load / call
/ indirect opcodes validating the pointed-to object's type before unsafe use) — a
separate, hot-path-sensitive effort. 1 of 590 mutants.

## Verdict

The loader is **robust to malformed BYTES and malformed STRUCTURE** (the two
structural SEGV classes are fixed; the DoS hardening is validated). The remaining
exposure is the general untyped-ref type-confusion class, documented above. A
permanent loader-fuzz harness (`tools/`) replaying the kept mutants would fence
regressions.
