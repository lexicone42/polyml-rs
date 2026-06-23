# Apple Silicon cross-arch demo — runbook

> **Status: validated on real Apple Silicon.** A heap image built by polyml-rs on
> x86-64 Linux executed on an arm64 Mac in **1,110,805 steps → `Tagged(0)`**,
> byte-identical to the x86-64 reference; and `fact 10` → `3628800` ran through the
> self-bootstrapped `polyexport` REPL image. (The opt-in `--jit` path, Cranelift
> targeting arm64, also ran clean.) The steps below reproduce it.

**Goal:** demonstrate the headline portability claim of polyml-rs — *a heap image
our Rust runtime builds on x86-64 Linux executes unchanged on arm64 macOS,
byte-for-byte identically.* This exercises **cross-architecture and cross-OS at
once**, on real hardware (no emulation). You need an Apple Silicon Mac; the build
is native (no QEMU).

---

## Why this works (one paragraph of context)

polyml-rs is a Rust rewrite of PolyML's **interpreter** (not a native-code
compiler). Heap images are PolyML's *portable export* ("pexport") format:
**bytecode** (identical bytes on any arch), inter-object pointers stored as
**object IDs** (resolved at load, not addresses), and runtime calls linked **by
name** (re-resolved every load). There is **no native machine code in the image**
to relocate. x86_64 and arm64 are both 64-bit little-endian, so the same image
loads and runs unchanged. The `--jit` path (Cranelift) is **opt-in** and **not
used** here — plain `poly run` is a pure interpreter, which is the portability
story. So this demo needs no codegen, just: build the interpreter natively on the
Mac, then run an x86_64-built image through it.

---

## Prerequisites

- An Apple Silicon Mac (M1/M2/M3/…), arm64.
- **Xcode Command Line Tools** (for the system linker/SDK): `xcode-select --install`
  (skip if `clang --version` already works).
- **Rust via rustup**: `curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh`
  then restart the shell. The repo pins the toolchain in `rust-toolchain.toml`
  (1.96.0); `cargo` will auto-install/select it on first build. Confirm with
  `rustc --version` inside the repo → expect `rustc 1.96.0`.
- `git`.
- **No QEMU, no `cross`, no Docker** — this is a native build.

---

## Step 0 — get the repo + the two image files

### 0a. Clone the repo
```sh
git clone https://github.com/lexicone42/polyml-rs.git
cd polyml-rs
```
(If the repo is private, the user authenticates first: `gh auth login`, or use an
SSH/HTTPS token.)

### 0b. Get the vendor images (THE ONE MANUAL STEP)
The two heap images are **git-ignored** (large binaries, not in the repo). They
must be copied from the Linux dev box (or wherever they were built):

| File | Size | What it is | Needed for |
| --- | --- | --- | --- |
| `vendor/polyml/bootstrap/bootstrap64.txt` | ~1.8 MB | the stage-0 PolyML compiler image (checked in upstream; may already be present if the clone included `vendor/`, but `vendor/` is git-ignored here so usually NOT) | demo A (load+exec proof) |
| `polyexport` (place at repo root, or anywhere — you pass its path) | ~13 MB | a full SML system image **self-bootstrapped on x86_64 Linux** (basis + a working REPL) | demo B (the headline REPL) |

Transfer however is convenient — `scp` from the Linux box, AirDrop, a USB stick,
etc. Example with scp:
```sh
# from the Mac, pulling from the Linux box (adjust host/paths):
mkdir -p vendor/polyml/bootstrap
scp user@linux-box:/path/to/polyml-rs/vendor/polyml/bootstrap/bootstrap64.txt \
    vendor/polyml/bootstrap/bootstrap64.txt
scp user@linux-box:/path/to/polyml-rs/vendor/polyml/polyexport ./polyexport
```
The build needs **neither** image; only the demos do. If you only have one, run
whichever demo it supports.

---

## Step 1 — build the interpreter natively (arm64-apple-darwin)

```sh
cargo build --release -p polyml-bin
```
- Builds `target/release/poly` for the Mac's native target (`aarch64-apple-darwin`).
- Pre-vetted clean for macOS: the only platform-specific code is `#[cfg(unix)]`
  `getrusage` (macOS satisfies it), and the JIT/Cranelift is gated behind `--jit`
  so a plain build/run never invokes it.
- Expected: `Finished release [optimized] target(s)` with no errors. (Warnings are
  fine.) First build also compiles deps incl. `polyml-jit`/Cranelift — that's
  expected and harmless; it just isn't exercised unless you pass `--jit`.

Sanity-check the binary is arm64:
```sh
file target/release/poly      # → "Mach-O 64-bit executable arm64"
```

---

## Step 2 — the demos

### Demo A — an x86_64-built image LOADS + EXECUTES on arm64 (`bootstrap64.txt`)
```sh
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt
```
**Expected:**
```
Loaded vendor/polyml/bootstrap/bootstrap64.txt
  RTS patch: … resolved, 0 unresolved
Executing (cap … steps)…
Executed 1110805 bytecode step(s).
Result: Tagged(0) — clean return
```
**The portability proof is the step count.** On x86_64 Linux this same image runs
in **1,110,805** steps (current build) → `Tagged(0)`. If the Mac reports the
**same step count** and `Tagged(0)`, execution is **byte-for-byte identical across
arch+OS** — that is the headline. (The exact number can drift build-to-build; what
matters is it MATCHES the x86_64 reference for the same commit, and ends
`Tagged(0)`. Ask the dev-box side to confirm the current x86_64 count if unsure.)

### Demo B — the headline: a self-bootstrapped REPL image runs `fact 10` on arm64
```sh
echo "fun fact 0 = 1 | fact n = n * fact(n-1); fact 10;" \
  | ./target/release/poly run polyexport
```
**Expected (a real SML REPL):**
```
Poly/ML 5.9.2 Release (Git version polyml-rs)
> val fact = fn: int -> int
> val it = 3628800: int
Result: Tagged(0) — clean return
```
`polyexport` was **self-bootstrapped on x86_64 Linux** (the 7-stage chain run on
our Rust runtime). Seeing `val it = 3628800: int` here means that image — type
inference, recursion, the basis, the whole REPL — is **executing on arm64 macOS
unchanged**. That is the dream: portable cross-arch heap images, demonstrated on
real Apple Silicon.

---

## Optional — exercise the Cranelift JIT on arm64 (NOT part of the portability claim)

The portability story is the interpreter; the JIT is a separate, opt-in path. If
you want to confirm Cranelift codegen also works on arm64:
```sh
./target/release/poly run --jit vendor/polyml/bootstrap/bootstrap64.txt
```
Expect the same `Tagged(0)`. (On x86_64 the JIT is a slight (~2%) speedup after
the Phase 0 work, but it's primarily a correctness testbed — don't read timing
into a single arm64 run. The step count will be *lower* than the interpreter's:
JIT'd functions run as native code and don't tick the bytecode-step counter, so a
lower count with the same `Tagged(0)` is expected, not a divergence. If it SEGVs
or diverges, that's an arm64-JIT finding worth reporting, but it does **not**
affect the portability demo, which uses plain `poly run`.)

---

## What to report back

A short summary with:
1. `rustc --version` and `file target/release/poly` (confirm 1.96.0 + arm64).
2. Demo A: the exact `Executed N bytecode step(s).` line + the `Result:` line.
   State whether N matches the x86_64 reference (1,110,805 for the current build).
3. Demo B: the `val it = …: int` line (expect `3628800`) + the `Result:` line.
4. Anything unexpected, verbatim (errors, a different step count, a SEGV).

A clean run = **Demo A byte-identical step count + `Tagged(0)`, Demo B
`3628800`.** That is the cross-arch + cross-OS portability claim, proven on
hardware.

---

## Troubleshooting

- **`rustc` not 1.96.0:** run any `cargo` command inside the repo; `rust-toolchain.toml`
  pins it and rustup auto-installs. Don't override with `+stable`.
- **Linker / SDK errors:** `xcode-select --install`; retry.
- **`bootstrap64.txt` / `polyexport` not found:** they're git-ignored and must be
  copied over (Step 0b). The build does not need them; only the demos do.
- **`LoadError: WordSizeMismatch`:** would mean a 32-bit image on a 64-bit host (or
  vice-versa). Not expected here — both sides are 64-bit. If it appears, the image
  wasn't the 64-bit one; re-transfer.
- **Different step count than x86_64:** that would be a genuine portability bug
  (non-determinism across arch). Capture both counts + the image's commit and
  report it — that's exactly the kind of finding this demo exists to surface.
- **Demo B prints no `val it`:** ensure stdin is actually piped (the `echo | poly`
  form). An interactive `poly run polyexport` then typing also works; end with
  Ctrl-D.

---

## One-shot script (optional convenience)

```sh
#!/usr/bin/env bash
set -e
cargo build --release -p polyml-bin
echo "=== binary ==="; file target/release/poly
echo "=== Demo A: x86_64-built image on arm64 ==="
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt
echo "=== Demo B: self-bootstrapped REPL, fact 10 ==="
echo "fun fact 0 = 1 | fact n = n * fact(n-1); fact 10;" \
  | ./target/release/poly run polyexport
```
