# Read saved baseline obligations separately

As a PDD user, I want to see saved baseline obligations beside affected results, so that I can assess the remaining blocking work.

Proposed exit rule for review: target checks may exit 0 while C has a saved failure. That status proves only the selected checks. C still blocks the unchanged full-pass gate. Approve this convention or request a different affected-command status.

## Acceptance criteria

1. After affected Stories A and B pass, a separate baseline report retains Story C's saved failure with its original batch, Check ID, time and report link; it creates no current C result or paid C rerun.
2. Baseline history keeps older failures after newer passes or unsent records, distinguishes current, stale and unavailable original-batch source evidence, and shows missing or nonpassing evidence without inventing a pass, defect age or owner.
3. An affected command uses its selected results for the process exit status and clearly says it is not a full workflow pass. Saved reads and retries keep the original report snapshot, while all existing full-pass, approval, publication, code, merge and native-suite gates remain blocking.

## Rules to check

- A saved baseline observation is historical evidence. Never insert it into current batch rows, count new calls for it, erase an original failure, or use it to grant a full workflow pass.
- Source currentness compares the original complete batch selection. A stale original batch does not prove that C changed or that its defect predates this work.

## Coverage boundary

```pdd-boundary
prompts/cli/runtime-check-plan.prompt.md
```

The Runtime scenario checks supplied planning/report facts only. Native cases must establish actual Git/source selection, CLI effects, saved-history admission and unchanged gates. Neither set has run for this draft.
AC3 has no Runtime check. Exit status, saved snapshots and gate behavior remain
explicitly not checked; the native cases specify the required observations.
