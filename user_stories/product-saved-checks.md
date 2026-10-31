# Count manually checked product Stories

I can see current passing Story checks in product progress when I continue a run manually.

## Acceptance criteria

1. Four current saved server passes show server 4 of 4 and slice 1 4 of 13, with the other nine Stories not run, even while the server run has no completed workflow step or no workflow record exists.
2. A Story reported by both a workflow record and a saved check counts once; an unrelated S010 check never counts as S01.
3. Passing saved checks do not mark the server run merged and leave its dependent journey waiting for implementation to merge.
4. Reading product progress makes no Runtime request, changes no saved check and starts no workflow.

## Rules to check

Each planned Story counts at most once. Current evidence wins over older files;
the newest current result wins across local evidence sources. A failure or unknown
result cannot be a pass. Saved check progress never supplies implementation
completion or approval. Matching requires the exact Story ID token, so S010 is
not S01.

A planned Story may use saved checks from the product folder without a workflow
record. Only a verified local workflow authorizes its separate worktree; an
unverified link cannot supply a foreign root. Cwd-only evidence remains usable
without repairing that link or changing its unverified status.
