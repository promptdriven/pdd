# See whether an area agent started

As a developer starting a feature run, I want failed agent launches to be visible, so that I can fix my agent setup before expecting work.

## Acceptance criteria

1. Before an area agent is observed running, its chat stays starting, including during startup grace.
2. When an area agent exits with an error, workflow status retains its exit code and diagnostic, even if the agent was briefly observed running.
3. A recorded launch failure stays visible when Herdr later becomes unavailable.
4. An agent observed alive shows a running chat even when an earlier launch receipt exists.

## What must not change

- Starting a run keeps its assigned worktree and saved account choice.
- Missing agent evidence alone never authorizes another launch.

## Rules to check

- No elapsed startup time or absent agent alone may produce a failed or ended chat.
- A definite launch failure retains its code and diagnostic through unavailable inspections.

```pdd-boundary
prompts/cli/workflow-chat.prompt.md
```
