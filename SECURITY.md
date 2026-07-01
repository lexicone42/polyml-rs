# Security policy

## Reporting

Use GitHub's private vulnerability reporting ("Security" → "Report a
vulnerability" on this repository). If the issue is not sensitive — e.g. a
crash without memory-unsafety — a plain issue is fine too.

## Threat model — what counts as a vulnerability

- **A malicious heap image under `poly run --untrusted`.** This mode's contract
  is a clean halt: any memory-unsafety (out-of-bounds read/write, wild jump,
  use-after-free) reachable from a crafted image in `--untrusted` mode is a
  vulnerability. A reproducer image is the ideal report — see
  `tools/malicious-corpus/` for the shape.
- **Memory-unsafety reachable from SML *source*** (i.e. through the real
  compiler) in any mode is always a vulnerability.
- **Default (trusted) mode assumes the image is trusted.** Like upstream
  Poly/ML, `poly run <image>` without `--untrusted` executes compiler-produced
  bytecode without per-dereference validation. Memory-unsafety on a
  *hand-crafted* image in trusted mode is the documented trade-off, not a
  vulnerability — run foreign images with `--untrusted`.
- **`--untrusted` is memory safety, not a sandbox.** The image runs with the
  invoking user's ambient authority (filesystem, environment, stdout).
  Sandboxing is out of scope today; don't run hostile images you wouldn't run
  as an ordinary program.

The methodology behind these claims (loader fuzzing, the malicious-image
corpus, the deref-surface lint, the unsafe-block audit) is documented in
[`docs/correctness-and-safety.md`](docs/correctness-and-safety.md).
