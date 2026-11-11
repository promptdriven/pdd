# Read runs from a phone or service

As a person steering runs from my phone, I want a documented, versioned JSON list, so that my service can show what each run waits for without breaking on an undocumented field change.

## Acceptance criteria

1. `pdd workflow status --all --json` returns version 1 and runs matching the repository schema, including an empty list; an incompatible field change requires a new version.
2. Each run identifies the issue, worktree, title, workflow, agent, current area and unfinished step, PR numbers and URLs with draft and CI facts, known Story counts or unknown, current Herdr session/tab/pane, and the last saved change time.
3. Each run distinguishes a gate with its saved id, a question with its full saved text, stopped chat, failed or unconfirmed startup, and no wait. Completed and cancelled runs have no wait. A current question wins over a gate; startup failure wins over both. Unavailable inspection alone never proves a stopped chat.
4. A stopped chat has reason usage_limit, exited, or unknown; unclear stops never claim exit or usage exhaustion.
5. The JSON excludes private Try links, including links embedded in titles, questions and saved internal records. Text status and other JSON status formats keep their existing behavior; cancelled filtering and run ordering remain intact.

## What must not change

Approval still requires its existing authority. This adds no commands and makes no approval decision.

```pdd-boundary
prompts/cli/workflow-runner.prompt.md
prompts/cli/workflow-github.prompt.md
```
