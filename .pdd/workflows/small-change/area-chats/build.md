# Chat 2: build

Start only with PDD's recorded plan approval and accepted plan/test argv. If they are absent or stale, stop and report the missing input. Reuse accepted artifacts; do not rewrite independent expectations to match an implementation.

Coordinate change and verify in order using the current packet supplied by PDD. The later PR and merge rows describe runner-owned effects; do not wait for or invent a subagent packet for those effects:

| Stage | Subagent task | Main-chat report |
| --- | --- | --- |
| change | Implement the accepted scope; return the exact work handoff. | {{changeCommand}} |
| verify | Inspect checks and preserve the accepted test plan; return real evidence. | {{verifyCommand}} |
| open-pr | Review PR information only if PDD requests it. PDD creates the PR after accepted verification. | Runner-owned effect; no agent report required. |
| wait-merge | Discuss the recorded PR and feedback; the person merges through the normal process. | PDD observes merge; no agent report required. |

Wait for each accepted report before continuing. PDD runs the approved test argv itself, validates the exact current revision and opens the PR. Show only the PR identity PDD actually returns. If publication is uncertain, let PDD reconcile it; never repeat it yourself.

At the recorded merge gate, show the actual PR link/head, scope, check results, gaps and rollback. Ask:

“Is this PR ready for your normal merge process? You can say ‘I approve’ here in this chat, or run `{{approveCommand}}` in your terminal. Approval records your decision; merge the PR through your normal repository process. PDD will confirm the actual merge.”

Relay only a new, explicit user approval after that question with `{{approveCommand}}`. PDD checks the native user-message evidence. Refusal or ambiguous evidence leaves the gate pending. Neither approval nor ‘please merge’ authorizes this chat or a subagent to perform the merge. Do not invent a wait-merge report; PDD's real merge observation determines completion. Feedback that changes the head requires fresh checks through PDD before the revised PR can pass.
