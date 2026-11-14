# See the results saved with each workflow step

I can inspect a workflow and see the results saved with each step, including when a step has none.

Issue: https://github.com/promptdriven/pdd/issues/2922

## Acceptance criteria

1. `pdd workflow status 2922` shows each step's saved pddResults and says "none" for a step without results.
2. `pdd workflow status 2922 --json` associates each step with its saved pddResults and explicitly represents a step without results.
3. `pdd workflow view 2922` shows each step's saved pddResults and says "none" for a step without results.

## Rules to check

A step with an absent results field and a step with an empty results list both have none. Results remain associated with their own step, including a step in an earlier area. Showing only run-wide results or a Story count must not hide the saved per-step results.

For JSON, the message must parse as JSON and preserve each step's complete saved results list, including every record and field, in order. Each step with absent or empty input results has its own empty list. JSON layout remains free.

Keep existing status fields, grouping and refresh behavior, saved result formatting, and the passive local-read behavior of view. Agent notes remain separate from pdd's saved results.

## Review cases

The synthetic input has two areas, with code current and check in the earlier story area. No real check was executed. Run-wide results are empty.

| Step | Saved input | Required status / view | Required JSON association |
| --- | --- | --- | --- |
| reproduce | Results field absent | Its own "none" | reproduce has [] |
| check | FIRST and SECOND saved records | Both results belong to check | check has both complete records in order |
| verify | Empty results list | Its own "none" | verify has [] |
| finish | Results field absent | Its own "none" | finish has [] |

The [frozen native cases](../test/fixtures/workflow-step-results-2922-cases.json) contain the full synthetic input and independently authored expected mapping. The [assertion specification](../test/fixtures/workflow-step-results-2922-assertions.md) requires identity-based checks for all three commands and rejection of wrong-step assignment, invalid JSON, dropped payload fields/records, unrelated empty arrays and a generic "Gate: none" without each step's absence.

Coverage: the Runtime scenario is PARTIAL lexical coverage at a message-string boundary. Its substring checks cannot establish these associations, parsed JSON or full payload equality. The combined review package freezes every criterion; the native assertions still require implementation and execution in the Code stage. Neither draft lane is a behavior pass.

```pdd-boundary
prompts/cli/workflow-runner.prompt.md
prompts/cli/workflow-view.prompt.md
```
