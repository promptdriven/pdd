# Auto-stamp small-change checklist on workflow done

As a developer finishing a small-change workflow with `pdd workflow done`, I want pdd to automatically stamp mechanical checklist metadata while keeping item checks strict, so that late test or lint edits never require ad-hoc fingerprint scripts.

## Acceptance criteria

1. Finishing a small-change step with a checklist containing valid completed item "R1" and no schema version, run identifier, or source fingerprint writes the checklist once with version "pdd.small-change-checklist.v1", run identifier "run-fresh", and the current worktree fingerprint, returning status "recorded", stamped true, and 0 must-fix findings.
2. Finishing a small-change step when the checklist's recorded source fingerprint is older than the worktree after a late test edit writes the checklist once with the refreshed worktree fingerprint while keeping item "R1" intact, returning status "recorded", stamped true, and 0 must-fix findings.
3. Finishing a small-change step when a checklist item is missing its required quote writes nothing and returns status "malformed", stamped false, and 1 must-fix finding with code "malformed".
4. Finishing a small-change step when a "done" item has no completion evidence still blocks completion by returning status "recorded" and 1 must-fix finding for item "R1" with code "missing-evidence" rather than clearing the item.
5. Finishing a small-change step when the checklist already carries version "pdd.small-change-checklist.v1", the matching run identifier "run-valid", and the current worktree fingerprint writes nothing and returns status "recorded", stamped false, and 0 must-fix findings.
6. Finishing a step in a "feature" workflow run makes 0 checklist reads, 0 fingerprint lookups, and 0 checklist writes, returning status "skipped", stamped false, and 0 must-fix findings.

## Rules to check

- Auto-stamping refreshes only mechanical envelope metadata (schema version, run identifier, and source fingerprint). Forbidden: overwriting a checklist with malformed items, inventing missing completion evidence, or touching checklist storage during non-small-change runs.

```pdd-boundary
prompts/cli/workflow-small-change.prompt.md
```
