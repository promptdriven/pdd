# Follow a bounded authoring handoff

I can follow a short authoring example through a long check, repair and independent validation without losing ownership, progress or failures.

## Acceptance criteria

1. The example names each role's required context, exclusive writable files and durable handoff, while keeping governing instructions and unresolved evidence available.
2. The example waits for a long check on its original batch and tells me when the coordinator resumes, without treating unchanged tool progress as a new decision.
3. A delayed failure, repair and changed draft preserve the failed expectation and return to the required approval before further checking.
4. Independent verification and a long external native process preserve coverage, process identity, progress, cancellation and unsuccessful or unknown outcomes.

## Rules to check

A pending, interrupted, refused or missing result cannot become a pass. A CHECK batch cannot stand in for an external native process identity.

## Evidence boundary

Authoring instructions: [RUNBOOK §22](../RUNBOOK.md#22-bounded-handoffs-and-measurement). Cases: [native/manual cases](../test/authoring-guidance/authoring-orchestration-cases.json). These cases need independent native/manual execution. No executable Runtime entry owns agent context or physical process control. Prompt tests: NOT RUN; native/manual cases: NOT RUN. No model savings have been measured.
