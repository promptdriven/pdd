# Automatic run base

Own `src/autopilot-base.mjs`. The authorized scope is issue #3071 points 1–3. Preserve manual workflow base selection, approval, trust, checks, merge authority and stacked PR behavior. This module only reads; it never merges or changes branches or documents.

`selectAutopilotBase({cwd,defaultBranch}, ports={})` returns one branch name. Read `pdd.json` from cwd through `readConfig(cwd)` (native default: JSON filesystem read; a missing file means an empty config). Use `autopilot.base` when present; otherwise use the supplied repository default. A configured base must be a nonempty string naming a branch, excluding HEAD, options and full refs. Validate `refs/heads/BRANCH` with Git through `execFile`. Invalid config or an unavailable default fails without inventing a branch. Slash-separated names are allowed.

`checkAutopilotBase({run,pr}, ports={})` returns `{exitCode,message}`. `run` is the saved workflow run; `pr` is a positive PR number string. Refuse missing run identity, saved base or a PR not published by that run. Before any automatic merge, read that PR fresh from its saved repository, and require its actual base to equal `run.baseBranch`; stacked code PRs must first be retargeted through the existing merge route. The saved base remains the audit authority even if configuration changes later. Read the current default branch and all releases fresh. Choose the non-draft release with the newest published_at, including prereleases; no releases means only the default ancestry check applies. Use GitHub compare for default...saved-base and release-tag...saved-base. Each must have behind_by zero and status identical or ahead. Missing, malformed or failed observations refuse with a finite reason. Refuse an old or divergent base with a reason naming the branch and the default or release tag it lacks. After a merge the same read checks that the merged PR went to the saved base. A successful read reports the PR, base, default and release tag (or no release). Exit 0 means these base checks pass; exit 1 means refused. It does not approve a merge or prove tests or reviews.

All program calls use injected `execFile(file,args,{cwd})`; all config reads use `readConfig`. Native defaults use local filesystem and the counted native GitHub process adapter. No error includes raw external output or secrets. GitHub requests are read-only, with explicit repository paths and encoded refs. No cache is used for merge safety.

## Dependencies

- [Workflow runs](workflow-runs.prompt.md): required native generation context for the saved run repository, PR records and baseBranch supplied by the launcher.
- [GitHub calls](github-calls.prompt.md): required native generation context for the default counted process adapter.
