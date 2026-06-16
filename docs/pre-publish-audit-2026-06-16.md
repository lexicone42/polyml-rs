# Pre-publish repo audit — 2026-06-16

Read-only hygiene pass before pushing the repo to GitHub (the gate for the
Apple Silicon cross-arch demo). **Verdict: clean — safe to publish.**

## Results

| Check | Result |
| --- | --- |
| Tracked files | 326; `.git` 4.9 MB → clones are small |
| `.gitignore` | correctly excludes `/target`, `/vendor` (both confirmed ignored + untracked), `/scratch`, `*.pexport`, `*.bicimage`, `.claude/`, IDE/OS cruft |
| Secrets (sk-/ghp_/AKIA/PRIVATE KEY/password=) | none |
| Credential-ish files (.env/.pem/.key/id_rsa/credentials) | none |
| Hardcoded machine paths (`/home/...`, `/datar/...`) in `*.rs`/`*.sh`/`*.toml` | none |
| `/tmp` in shipped lib code | only in one `#[test]` (`rts.rs` set_command_args) — fine |
| Required release files | README.md, LICENSE-MIT, LICENSE-APACHE, PLAN.md, .github/workflows/ci.yml, rust-toolchain.toml — all present |
| Git history (large/orphaned blobs) | clean; largest-ever blobs are current tracked proof drivers (≤0.52 MB), no committed-then-deleted bloat or secrets |
| Commit-author identity | 420 commits, all `bryan <bryan.egan@gmail.com>` — consistent |

## Decisions (resolved 2026-06-16)

1. **Owner = `lexicone42`** (Organization; `bryanegan` is a member and can
   publish under it). `Cargo.toml` `repository` already matches.
2. **Author identity = GitHub noreply going forward.** Repo git config +
   `Cargo.toml` `authors` now use `3395267+bryanegan@users.noreply.github.com`
   (commit fixing this onward). History was **deliberately NOT scrubbed** — the
   421 pre-existing commits keep `bryan.egan@gmail.com`, by the author's choice
   ("people can find my email if they want"). Not a blocker.
3. **`vendor/` images don't travel via git** (git-ignored by design). Any
   consumer — including the macOS demo — needs `bootstrap64.txt` (1.8 MB) /
   `polyexport` (13 MB) transferred separately. The build itself fetches no
   images; only running the demos needs them.
4. **Large `.sml` proof drivers** (≤0.52 MB each) are legitimate (the actual
   Isabelle proofs). Some are known not-yet-consolidated foundation embeds
   (see CLAUDE.md) — a code-quality cleanup, not a publish concern.

## To publish (when greenlit)

```
gh repo create <owner>/polyml-rs --public --source=. --remote=origin --push
```

(or `--private` first). Nothing else is required — CI (`.github/workflows/ci.yml`)
runs fmt + clippy + build + tests on push.
