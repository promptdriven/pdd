# Proof review fixture cleanup

As a maintainer, I want the proof review fixtures to clean up every process they start, so that a failed or interrupted test does not leave processes running.

## Acceptance criteria

1. The interruption and recovery fixtures leave no process they started alive after success or failure, including a setup failure immediately after spawning and when the PID record is missing, empty, partial or malformed, or readiness times out.
2. Cleanup leaves the test runner and unrelated processes running, and the fixtures retain their interruption and recovery checks.

## Rules to check

A PID record is an observation, not the sole means of locating processes for cleanup; leaving a started descendant alive is forbidden.

```pdd-boundary
test/helpers/owned-process.prompt.md
```
