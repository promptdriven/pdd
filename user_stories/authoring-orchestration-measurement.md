# Compare authoring guidance on one frozen task

I can compare current and revised guidance on the same small task and see each role's usage, supplied context and unknown measurements.

## Acceptance criteria

1. Both arms freeze the same task, source, model, effort, tool versions, outcome rules and coverage; the baseline includes the current one-call wait.
2. The report separates the coordinator, each child and interpreter, with requests, cached and uncached input, output, wall time, outcome and provenance; missing usage stays unknown.
3. The report separates internal polling, saved-report reads and model-driven status requests, and distinguishes supplied context bytes from measured input or retained history.
4. Overlapping durations and cached or nested usage are not counted twice; synthetic exercises cannot establish savings, dollar claims or a numeric regression target.

## Rules to check

Unknown usage cannot be zero. Cached input already included in total input cannot be added again. Overlapping role durations cannot be added to arm elapsed time.

## Evidence boundary

Authoring instructions: [RUNBOOK §22](../RUNBOOK.md#22-bounded-handoffs-and-measurement). Cases: [native/manual cases](../test/authoring-guidance/authoring-orchestration-measurement-cases.json). These cases need independent native/manual execution. No executable Runtime entry owns agent context or physical process control. Prompt tests: NOT RUN; native/manual cases: NOT RUN. No model savings have been measured.
