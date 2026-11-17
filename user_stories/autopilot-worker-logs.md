# Follow an Autopilot worker

As a maintainer watching headless Autopilot in observe mode, I want to follow a worker by issue number, so that I can see what it is doing without taking over its terminal.

## Acceptance criteria

1. When issue 42 is second in the check queue, its suite status says "waiting for a check slot (position 2)" and shows the last activity time.
2. When that suite actually executes, its status says "tests running" and shows where to find its log and receipt.
3. An old running receipt without a confirmed live test process is shown as stale or uncertain, not as running tests.
4. When the worker switches to repair, the process status names "repair" and says whether its wrapper is running.

## What must not change

- Viewing progress or leaving the viewer does not stop a worker, approve anything or merge a pull request.

```pdd-boundary
prompts/cli/autopilot-logs.prompt.md
```
