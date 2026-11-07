# Resume work after a trusted PR review

As a maintainer, I can submit a review on a related PR and have Autopilot resume the waiting work once.

Draft for review.

## Acceptance criteria

1. In observe mode, a new submitted review from a trusted person wakes the idle agent once with that review, even when the issue and PR head are unchanged.
2. Unchanged repeat observations stay quiet. Untrusted reviews do not wake the agent or put their text in a later request.
3. A new trusted review stays pending while the agent is busy. When the agent is idle, Autopilot sends the pending work once. A failed delivery stays pending.
4. The tick reads reviews without a model call.

## Rules to check

- Use the current [launcher trust rule](../prompts/cli/autopilot-launcher.prompt.md#tick-and-the-skill-boundary) before delivery. Forbidden result: an untrusted review reaches the agent, including after trust is revoked while work is pending.
- Record delivery only after it succeeds for an idle agent. Forbidden results: lose a pending review or send the same unchanged review twice.

This Story depends on the [run and claim time-rule Story](autopilot-time-rules.md). Both timer and review wakes are in scope for this draft. Keep PR state and discussion wakes, start-up recipe, and person approval and merge rules.
