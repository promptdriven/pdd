# Keep the issue safe when stopping is uncertain

I can trust that cancelling or switching never leaves two agents working on my issue.

## Acceptance criteria

1. When the live agent cannot be confirmed stopped, cancelling its run refuses and preserves its saved state and issue claim.
2. When the live agent cannot be confirmed stopped, replacing its run refuses and starts no new run, preserving all work and PRs.

## Rules to check

Confirmation is necessary but insufficient: a failed or unavailable stop forbids cancelled-state persistence, claim release and replacement. No old work or PR changes. The runtime uses a failed stop receipt; real process stopping needs code verification.

Code verification must run the public runner with real temporary run files and an isolated issue claim. Check status.json and index/C3 cancelled state, journal updates, exact preservation of all other saved fields and worktree/branch/journal/artifact contents, no pushes or PR closures, stop-before-release ordering, replacement identity, and delayed done from the old worktree. Runtime records.save assertions inspect the writeRun input ledger; they do not stand for those real-store checks.
