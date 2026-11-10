# Continue after a guidance PR

I can review the code choice after my guidance-only PR is complete, then approve
that continuation separately without losing the work already recorded.

## Acceptance criteria

1. A guidance-only PR 1 can be explicitly approved with an intentionally reviewed empty prompt selection, and its later code choice waits for a separate approval.
2. After a change request invalidates that review and merged PR 1 completes the run, `pdd workflow done try` from its worktree displays and durably saves the current code-choice review, including an empty selection, without approving, publishing, allocating a chat or changing progress.
3. After that current review is shown, a later explicit scoped approval starts the normal validated code continuation once, preserving the original run, PR-1 identity, publication head, owned paths, prior progress and approval evidence. After the code decision is saved, PR 1 refreshes its description and saved readable facts with the current approval and PR state.
4. An absent review refuses approval even when no prompts are selected; stale or revoked reviews and substantive prompt changes still require a current review and new approval.
5. Cancelled runs and runs completed in code remain ended; attempting review recovery or approval cannot start code, change progress or add approval evidence.

## What must not change

Keep the original run and worktree, selected base, PRs, branch history, completed
steps, gate identity and prior approvals. Refreshing the review preserves its
completed-at-PR-1 state and changes only the current review and save metadata.
The later code approval may refresh PR 1's description and saved readable facts;
it must retain PR identity, publication head, owned paths and earlier evidence.
Existing ordinary prompt/code flow, wrong-run protection, strict terminal policy,
configuration checks and publication recovery keep their behavior. Earlier PR-1
approval, inspection and change requests never authorize code. No new global gate,
exact approval phrase, account management or batch-permission behavior is added.

## Rules to check

An intentionally reviewed empty selection is present review evidence; a missing
review is not. Only a fresh recovery for the same completed-at-PR-1 run and ready
code-choice gate may save its current review. Recovery must preserve completion
and prior evidence. Approval must follow display, match the current gate and
review, and satisfy existing policy before any code branch or chat effect.
After successful source validation and the durable code decision, continuation
refreshes PR 1 using the existing description-refresh route. A refused approval
cannot publish code consent. This later refresh is separate from review-only
recovery, which preserves the full PR record.
Forbidden results include implicit approval from emptiness, reuse of PR-1 consent
for code, progress from refresh, resurrection of an ended code/cancelled run, or
effects from a stale, revoked, wrong-run or concurrently changed gate.

## Verification boundary

The [native cases](../test/fixtures/recover-guidance-code-review-cases.json) derive
their inputs and expected observations from issue #2979. They are a native case
inventory, not an executable Interpreter scenario. The owning
[workflow runner](../prompts/cli/workflow-runner.prompt.md) has no Runtime entry
for the real done/approval operations or complete bindings for durable run writes,
Git, publication and Herdr. Those effects are unbound and need real CLI tests with
temporary Git/state and deterministic executable transports. No check-only API,
Runtime verdict or live continuation is claimed.
