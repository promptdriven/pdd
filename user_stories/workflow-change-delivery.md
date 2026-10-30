# Keep my workflow change request while a chat starts

I can request changes immediately after approving an area and trust pdd to wait briefly for the new chat, or keep my exact request and show me how to retry.

## Acceptance criteria

1. Immediately after `pdd workflow approve 2` starts the prompt-pr chat, `pdd workflow changes 2 "Add the retry example"` waits within the chat's 30-second startup window and submits that request once when the original chat becomes ready.
2. If that chat never becomes ready, pdd stops waiting by the startup deadline, reports that it is still starting, keeps the exact request durably, and shows how to retry.
3. Retrying the same pending request sends it once; a different request waits behind earlier pending requests, and acknowledged requests are never replayed.
4. A blocked or unavailable chat keeps the exact request and shows an actionable recovery step; an uncertain acknowledgement is disclosed and never blindly resent.
5. Requests preserve spaces, quotes and line breaks. A request submitted while the agent is working reaches the same chat once without waiting for its current turn to finish.
6. Changes keep approval gates open, answers retain their existing meaning, and delivery neither approves nor advances an area, restarts an agent, nor overwrites progress or newer questions saved while it waits.

## Rules to check

- The readiness deadline is 30 seconds after the latest start or resume, not a fresh 30 seconds on every retry. Outside that window, missing agents are reported promptly.
- Duplicate suppression applies only to the same pending text, kind and original target. Repeating an acknowledged text is a new request. Never send a later request for the same area and pane ahead of a pending or uncertain one. Pending requests for an earlier target stay with that target; an independent target may accept new requests.
- Save custody before transport; a failed save must send nothing. A replacement area or pane must never receive the earlier target's request.
- Submission acknowledgement is not proof that an agent acted on the request. Native waiting-stub evidence checks consumption; actual Codex/Claude turn semantics need separate evidence.
