# Contributing

This is a research artifact with a small maintainer surface. **Issues are very
welcome** — bug reports, faithfulness divergences from upstream Poly/ML,
reproduction failures, portability reports from other architectures. For
anything non-trivial, please open an issue before a PR so we can agree on
direction; day-to-day development happens by direct push, so PRs may be adapted
rather than merged as-is.

Before proposing a change:

- `tools/regression.sh fast` must pass (build + all always-on tests, ~2 min,
  no vendor data needed).
- Interpreter/runtime changes: keep the upstream `bytecode.cpp` line-range
  citations on opcode handlers, and read the gotchas in
  [`CLAUDE.md`](CLAUDE.md) first — especially the RESET variants, the RTS
  calling conventions, and the RTS registration-**order** hazard (dispatch
  tokens are baked into warm checkpoints by order; never reorder `rts.rs`).
- Faithfulness-affecting changes should come with a differential-oracle case
  (`tools/diff-oracle.sh`, corpus under `tools/diff-corpus/`) where feasible.
- Security reports: see [`SECURITY.md`](SECURITY.md).
