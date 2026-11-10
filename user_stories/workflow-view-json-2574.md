# Read a workflow gate as data

As a person steering a run from my phone, I can read its current gate, review links and approvals as JSON before deciding what to approve.

## Acceptance criteria

1. A JSON view at a gate contains version 1, the gate id and its current chat message, links to Stories, plan and PRs, and recorded approval actors and times.
2. When no gate is open, the gate is null and links and approvals remain available.
3. No private Try link appears in the JSON, including inside a message or an approval actor.

## Rules to check

The gate is the active saved gate; an ended run has no gate except its optional code decision. If the current chat cannot be identified or read, its message is null. A private Try URL must not survive in any returned field, including a gate message, link or actor. Forbidden: a stale gate message, private Try URL, or invented approval actor or time.

```pdd-boundary
prompts/cli/workflow-view.prompt.md
```
