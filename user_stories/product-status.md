# Track product progress

I can see which planned Stories passed on current files and which need another check.

## Acceptance criteria

1. With P01 current and P02 passed only on older files, phone shows one pass, one stale and two not run out of four Stories.
2. The unrelated P010 result is not counted as P01, and the server and barista each have four not-run Stories.
3. Slice 1 includes the twelve part Stories and J1 once, with one pass, one stale and eleven not run.

## Rules to check

Only a pass bound to current files is a local current pass. P010 must never satisfy P01. A stale pass must not appear as current.

Only this run's same-repository PRs supply its progress. A later code PR with no
check results must not hide the prompt PR's results or change their attribution.
Forks, comments and another run's references cannot supply progress or completion.
After implementation merges, freshness follows current base-branch files, not
the finished run's retained worktree. An unavailable base is unverified, with a
warning. A visible dependency cycle names its closed path.

Status names the local comparison base and says to run git pull to see changes
merged on GitHub. Only a rejected PR claiming this run's marker produces a
provenance warning; ordinary cross-references from other runs stay quiet.
