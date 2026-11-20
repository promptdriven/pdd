# Filter unclaimable issues before Autopilot claims them

As a repository maintainer running Autopilot, I want intake to pre-flight reject or park cross-repo, human-decision, and unverifiable issues before claiming them, so that Autopilot stops spending build tokens on work it cannot finish cleanly.

## Acceptance criteria

1. Before claiming an issue that requires coordinated edits in another repository such as `pdd_cloud` or `pdd-workflow`, Autopilot rejects it as cross-repo, marks it `needs-other-repo`, and records a crisp skip reason.
2. Before claiming an issue that asks an unanswered product, pricing, or UX policy decision, Autopilot parks it for a person with `pdd:needs-decision`, asks one concise question, and records a crisp skip reason; once a trusted person answers the decision in a comment, Autopilot allows it.
3. Before claiming an issue whose required verification depends on an external service, live production credentials, or manual human QA unavailable to the worker without authorizing a local test boundary, Autopilot parks it for a person with `pdd:needs-decision` and records a crisp skip reason.
4. A valid single-repo bug or feature that mentions another service only for context, cites a pasted error log in a code fence, or can be verified with local tests passes pre-flight without being skipped.
5. Recorded pre-flight skip reasons roll up into exact counts per reason category alongside Classifier Conversion ("3/4 (75.0%)" when 3 of 4 taken issues merged or reached would-merge, or "0/0 (n/a)" when 0 issues were taken) so metrics can report intake filter precision.

## What must not change

- Shadow mode records pre-flight skips locally without writing labels or comments to GitHub.
- Valid single-repo issues with new local files or local automated test verification remain claimable.

## Rules to check

- An issue rejected or parked at pre-flight must never be claimed for a build. Forbidden: classifying a quoted or fenced log mention of another repository as cross-repo, or parking an engineering bug fix that has no product, pricing, or UX policy question.

```pdd-boundary
prompts/cli/autopilot-intake-preflight.prompt.md
```
