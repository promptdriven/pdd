# Target single scenarios and recover check batches

As a developer running `pdd test` in the terminal, I want to target one scenario file, retry every non-passed scenario from a saved batch, clear stale reservations automatically, and preview `--affected --files`, so that check verification stays fast and reliable.

## Acceptance criteria

1. `pdd test --affected --files` (and with `--json`) previews the affected Stories, scenario files, and upload closure, exits with code 0, and makes 0 AI calls.
2. `pdd test tests/split.a.json`, `pdd test --files tests/split.a.json`, and `pdd test --target code tests/split.a.json` on a Story split across sibling scenarios `tests/split.a.json` and `tests/split.b.json` execute only `tests/split.a.json` against its owning Story and prompt closure, exit with code 0 when its checks pass, and still fail closed when any Story criterion is uncovered across all sibling scenarios.
3. `pdd test --retry-unresolved 20261125-100000-ab12` reconciles expired reservations on that saved batch, skips scenarios that already passed, and re-runs all non-passed scenarios (`partial`, `unknown`, `not_run`, and `failed`), or exits with code 0 and 0 AI calls when every scenario in the batch already passed.
4. Before dispatching a new `pdd test` batch, stale prior reservations for the repository are automatically reconciled with a bounded fail-open timeout, while clean repositories with no stale reservations perform 0 reconciliation calls.
5. Invalid option combinations (`pdd test --affected --files --lf`, `pdd test --affected --files split`, or `pdd test --retry-unresolved not-a-batch`) print a usage error to stderr, exit with code 2, and perform 0 AI or reconciliation calls.

## What must not change

- Existing `pdd test --retry BATCH` semantics (retrying only confirmed unstarted checks with unchanged source) remain intact.
- Existing `pdd test --reconcile` and `pdd test --reconcile-stale` commands remain intact.
- Full-Story runs (`pdd test STORY`, `pdd test`) keep complete Story criterion requirements and never mark an incomplete Story as passed.

## Rules to check

- Single-scenario targeting never executes unselected sibling scenarios and never writes a full-Story pass entry into the complete-pass cache.
- `--retry-unresolved` never re-runs confirmed `passed` scenarios and never drops `partial`, `unknown`, `not_run`, or `failed` scenarios.
- Auto-reconciliation never aborts a new check batch when reconciliation fails or times out, and performs 0 reconciliation calls when no stale reservations exist.
