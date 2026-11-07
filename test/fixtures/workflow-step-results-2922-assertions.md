# Frozen assertions for saved workflow step results

This is a requirement-authored Code-stage test specification, not executable test code or an observed result. Its [case data](workflow-step-results-2922-cases.json) freezes the complete synthetic input and expected per-step mapping for [the Story](../../user_stories/workflow-step-results-2922.md). The Runtime scenario is PARTIAL lexical coverage; these native assertions supply its missing semantic expectations for review, not a claimed pass.

## Public boundary and setup

Call each case's real public export with its stated input and native outside ports: `src/workflow-runner.mjs` exports `runStatus(options, ports)` for text and JSON, and `src/workflow-view.mjs` exports `viewRun({ref,cwd}, ports)`. Observe their existing `{exitCode,message}` replies. Add no parser, snapshot, renderer or replay operation to the product.

The complete `input.selectedRun` is a logical supplied resolver reply, matching the hosted scenario. `input.localReads` freezes the remaining supplied Runtime replies; it does not create a native `runs.resolveRun` or `files.*` injection API. Native production selection and physical port mapping are UNPROVED. Native integration must create records through real `startRun` and `stepDone`, supplying the frozen result lists through the existing result-reader port when completing check/verify. Read back the saved projection to establish setup, separately from display assertions. Never write raw run, gate or proof records to reach the fixture. Resolve generated paths, IDs and clock anchors through the supported setup; do not substitute generated display output for expectations.

Native setup must retain both areas, code as current and check in the earlier story area, as well as the absent reproduce/finish fields, explicit empty verify list and two check records. Any needed area transition or ended-run setup must use supported public APIs under an isolated synthetic harness; it cannot invent person authorization or silently reduce this case to a single area. An unavailable setup/binding is an unrun obligation, not permission to edit the expected mapping. No native setup or display execution is included in this draft.

## Required observations

Each of the three operations independently requires exit code 0 and every row of `expected.byStep`. Match the selected run by repository and issue, then each step by its identity (and owning area); do not match by array position, summary token, current-area membership or counts alone. A label in an unrelated note is insufficient.

For **JSON status (AC2)**:

- Parse the entire message as JSON; a parse error fails even when all lexical markers appear.
- Implement identity-driven association extraction in the Code-stage native test for the public layout actually chosen. It is test assertion logic, not a new product export. This specification chooses no JSON property path, container shape or serialized whitespace.
- Require a represented result list for every expected step. Deep-compare check's extracted list to its complete literal `expected.byStep` list: both records, saved order, every property/value and nested requests array. Do not project to summaries or a selected subset of fields. Missing, added or changed saved payload fields fail equality.
- Independently require reproduce, verify and finish to each have the explicit JSON list `[]` associated with that step. Missing, null or an empty array under an unrelated field cannot satisfy a row. A result reassigned or additionally attributed to another step fails.

For **text status (AC1)** and **passive view (AC3)**, apply the same expectations separately to each message:

- Extract each step's displayed results by its explicit label and bounded section/row association. Do not use independent whole-message searches or a span that can cross into the next step. Support the chosen public text arrangement without mandating a new one.
- Require both distinct saved check results under check, including its earlier story-area identity. Follow the existing results-reader formatting contract. Each full summary marker must belong to its own formatted result there; result text only in agent notes, run-wide results or under verify does not count.
- Independently require a saved-results "none" observation for reproduce, verify and finish. Each must be linked to that step's results, not its agent summary. A generic gate/approval/run-wide none cannot satisfy any of these three observations.
- Reject saved check results attributed to reproduce, verify or finish, and reject a missing check association even when both markers appear elsewhere. Keep the existing separation of saved results and agent notes.

## Counterexamples that the later assertions must reject

The data's `rejectedCounterexamples` are declarative assertion-design controls, not executed mutations. Apply each independently to an otherwise satisfying display; exercise each listed operation and each independent field/step. They retain the required expectations. Their wording describes defective observations without prescribing JSON layout.

| Counterexample | Required rejection |
| --- | --- |
| wrong-step | Both check records moved under verify, despite all tokens remaining |
| invalid-json | Token-rich message that fails JSON parsing |
| lost-field / changed-payload | Either record loses kind, batch, at, summary or requests, or changes a nested value |
| lost-record | Either complete record is missing or saved order changes |
| missing-individual-none | Each of reproduce, verify and finish is missing in turn, despite the other two being correct |
| unrelated-empty-array | prs or requests supplies [] while per-step empty lists are absent |
| generic-none | Gate: none remains while the three step-specific none observations are absent |

Code-stage verification must demonstrate these controls reject the defects; authored controls alone establish no execution. Report AC1/AC2/AC3 separately, with any unavailable extraction, setup or assertion unproved. Existing grouping/status refresh, CLI dispatch and passive physical reads still need their own native verification; the ended supplied world and synthetic Runtime ports do not prove those effects. No hosted/interpreter execution, native display fix or approval is claimed by this package.
