# Native verification in a workflow

As a developer, I can use native verification for an existing public boundary
that Runtime cannot admit, while the workflow keeps its Story and publication
gates.

## Acceptance criteria

1. Current native evidence can support an approved Story without a Runtime scenario; opening PR 1 then requires a separate later approval.
2. Missing or stale native evidence, and missing or failed Runtime checks for other selected Stories, do not open that gate.
3. A changed Story returns to its Story approval, and strict mode retains its terminal approval.
4. I can retain an earlier native check against its committed source as before-the-fix evidence; it cannot serve as current evidence or approve publication.

The [native workflow cases](../test/native-gate-repair.test.mjs) exercise the
workflow's saved evidence and approvals at its public functions. They do not
claim a Runtime entry for native file and Git custody.
