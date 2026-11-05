# Workflow storage contention regression

Own `test/workflow-concurrent-progress.storage.test.mjs`, the native Node test
module run by `node --test test/workflow-concurrent-progress.storage.test.mjs`.
Preserve its other storage checks and the existing production contract. Correct
the compatible whole-write contention test without changing runtime wait policy.

Hold a real `updateRun` callback under ordinary ownership while a compatible
`writeRun` attempts its whole-record save. A worker's `attempting` message does
not establish that it acquired ownership or began waiting. Observe that the
whole write cannot publish inside the held callback, then release and record
both outcomes. Use deterministic synchronization or check both permitted
outcomes; do not rely on fixed sleeps or a deadline for worker scheduling.

A successful whole write must have published only after the callback committed
and must retain its own intended whole-record effect. A finite contention refusal
must report the failure and leave the callback's committed state intact. Do not
call a refusal a successful write or hide a successful lost update. An explicit
whole-record save does not infer an untracked caller's intent. Preserve the
separate public-command checks that successful unrelated progress survives.
Capture worker errors and outcomes in failures, and release and terminate workers
on every exit. Do not bypass ownership, add a production test API, or change the
runtime wait policy. If evidence shows the original no-lost-update contract is
violated, report that product defect for review.

## Dependencies

- [Storage test](../../test/workflow-concurrent-progress.storage.test.mjs), [worker](../../test/helpers/workflow-concurrent-storage-worker.mjs), and [fixture](../../test/helpers/workflow-delivery-fixture.mjs): required for authoring and native verification.
- [Storage contract](../cli/workflow-runs.prompt.md#concurrent-record-updates) and [runner contract](../cli/workflow-runner.prompt.md#preserve-concurrent-progress): required product policy for authoring and native verification.
- [Original Story](../../user_stories/workflow-concurrent-progress.md) and [case inventory](../../test/workflow-concurrent-progress/cases.json): required preservation context for native verification.

## Native boundary

This module registers Node tests and exports no callable operation. Worker and
Atomics scheduling and native filesystem ownership are unbound to the
Interpreter. No simulated outcome or prompt pass is claimed.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"056e9454c030e0a77e581b15f693ffd0f53375ced94c541d7d71a08034f6a915","entries":[],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":[]}
```

</details>
