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

## Notes / decisions before the push (not blockers)

1. **Author email becomes public.** `bryan.egan@gmail.com` appears in
   `Cargo.toml` (`authors`) and on all 420 commits. This is the existing git
   identity and is intended-public for an authored open-source repo — just a
   heads-up, not a leak.
2. **Repo owner.** `gh` is authed as `bryanegan`; `Cargo.toml` `repository`
   points at `lexicone42/polyml-rs`. Confirm which owner before
   `gh repo create` + push.
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
