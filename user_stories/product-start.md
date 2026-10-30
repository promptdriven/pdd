# Start a planned run once

I can start a planned run through its existing issue or prepare the issue without starting work.

## Acceptance criteria

1. Starting phone-1 reuses issue 81 and starts one normal feature run with the chosen claude agent.
2. Preparing phone-1 with --no-run reuses issue 81 and starts no additional workflow.
3. An unknown run returns a nonzero result and starts no workflow.

## Rules to check

Use the exact run marker before creating an issue. --no-run must not start work. An unknown run must not mutate GitHub or start a workflow.
