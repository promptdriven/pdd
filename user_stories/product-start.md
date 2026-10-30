# Start a planned run once

I can start a planned run through its existing issue or prepare the issue without starting work.

## Acceptance criteria

1. Starting phone-1 reuses issue 81 and starts one normal feature run with the chosen claude agent.
2. Preparing phone-1 with --no-run reuses issue 81 and starts no additional workflow.
3. An unknown run returns a nonzero result and starts no workflow.
4. Starting barista-1 when no issue has its marker makes one issue whose title names barista-1 and B01, B02, B03 and B04, whose body names product #50, prompts/barista, the contracts and the run marker, then starts one feature run.

## Rules to check

Use the exact run marker before creating an issue. --no-run must not start work. An unknown run must not mutate GitHub or start a workflow.
