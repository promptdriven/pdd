# Refuse an action for an old workflow state

As a person acting on a workflow from another device, I want to send the gate or step I saw, so that a late action cannot affect a run that has moved on.

## Acceptance criteria

1. Approve, changes, cancel and open accept an expected gate ID or step. A matching expectation preserves the action's existing behavior.
2. A mismatch refuses with exit code 3 and names the current gate and step, including when either is absent. If both expectations are supplied, both must match.
3. A refusal leaves the run state, approvals, chat and files unchanged, including for a request to open an old area or a new chat.
4. Without an expectation these actions behave as before. The documented exit code lets a caller recognize a stale action.
