# Workflow completion overlap regression

Own `test/workflow-concurrent-progress.overlap.test.mjs`, the native Node test
module run by `node --test test/workflow-concurrent-progress.overlap.test.mjs`.
It observes public workflow completion results and the saved run in a private
fixture. Preserve its successful-completion union regression and sequential
controls while making failures explainable and stale-selection schedules
deterministic. This contract changes the test harness only.

## Diagnostic evidence

First improve the assertions that inspect worker failures and completion exit
codes. A failing assertion must identify the pair, mode, worker and step names,
both workers' full returned messages or errors and exit codes, and the observed
saved completion values. Include equivalent context when the union assertion
fails. Preserve the original returned message; a bare `1 !== 0` cannot explain
an ownership refusal. Do not turn a failure into success or hide missing records.

## Stale-selection schedule

For each overlapping pair, hold both invocations after they selected the same
initial run and before ordinary ownership. Give them separately controlled
releases. Release one, await its successful completion, then release the other
with its stale selection. Exercise both release orders across the small-record
and large-summary cases. Both must succeed and retain their full completion
records according to the [product owner](../cli/workflow-runner.prompt.md#preserve-concurrent-progress).

Retain the four sequential controls, sixteen small-record overlapping pairs and
sixteen pairs with a prior 65,536-character summary. Check both new records and
the unchanged prior record, rather than only counting keys. Keep worker errors,
barrier timeouts and unsuccessful saves as failures with diagnostic context.
Release held workers and terminate them during cleanup, including failure paths.

Separate release removes the unconditional simultaneous-lock-acquisition
assumption; it still exercises overlapping stale run selections. It does not
prove simultaneous acquisition. Keep the existing native ownership contention
coverage; its permitted failure behavior belongs to the
[storage owner](../cli/workflow-runs.prompt.md#concurrent-record-updates).
Do not add retries that can hide a lost successful completion, lengthen product
ownership waits, bypass ownership or add a production test API. If diagnostics
show a completion returned success but was lost, report that product defect
and stop this test-only correction for review.

## Dependencies

- [Test module](../../test/workflow-concurrent-progress.overlap.test.mjs), existing invocation and assertions, required for authoring and native verification.
- [Worker helper](../../test/helpers/workflow-concurrent-done-worker.mjs), existing first-clock hold and public completion call, required for authoring and native verification.
- [Fixture](../../test/helpers/workflow-delivery-fixture.mjs), private Git/HOME and external replies, required for authoring and native verification.
- [Runner contract](../cli/workflow-runner.prompt.md#preserve-concurrent-progress) and [storage contract](../cli/workflow-runs.prompt.md#concurrent-record-updates), required product policy for authoring and native verification; this module does not redefine it.
- [Ownership tests](../../test/workflow-concurrent-progress.ownership.test.mjs) and [native inventory](../../test/workflow-concurrent-progress/cases.json), existing contention and union coverage, required for native verification.

## Native boundary

This module registers a Node test; it exports no callable module operation.
Worker/Atomics barriers, Node assertion failures and real ordinary-record writes
are unsupported native effects here. Supplying a fixed-answer worker port would
only replay supplied outcomes; it cannot establish where the real workers held,
which assertion failed or what native record survived. No executable Interpreter
entry is declared, and no prompt pass is claimed for these obligations.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"918ffbf96ddfc37c2c0369d30858ba0ad1e61d1140ef7f228f22f387b70104d9","entries":[],"calls":[],"resources":[],"limits":{"max_steps":1,"max_model_calls":1},"conventions":[]}
```

</details>
