# See whether my workflow change request was taken up

I can see when pdd delivered my change request and whether the agent has explicitly recorded what it changed for that request.

## Acceptance criteria

1. When my change request reaches the chat, the chat and my delivery receipt identify the same request. My receipt shows its saved delivery time and acknowledgement state. A retry that observes delivery shows the saved identity and time without another send. Pending or uncertain delivery never claims success.
2. Workflow status lists delivered changes not yet taken up. Detailed and JSON status also show acknowledged changes with the agent's saved note and time, in request acceptance order. Unknown delivery times stay unknown; a saved time of zero remains known. Answers and undelivered requests are excluded.
3. From the active run's worktree, the agent can explicitly acknowledge one delivered change with a nonblank short note. Repeating that acknowledgement preserves its first saved note and time, including concurrent calls. An earlier area's delivered request in that same run is allowed.
4. Invalid or missing input, unknown or other-run requests, answers, undelivered requests, ended runs and calls outside the run worktree fail without recording uptake. Journal failures say visibility or acknowledgement is unavailable rather than claiming success or an empty list.
5. Completing a step or reaching a review gate warns about each delivered change still without an acknowledgement, with its identity and delivery time. The warning does not block normal progress or add an approval gate. A generic completion summary never acknowledges a request.
6. Acknowledgement preserves request custody and all workflow progress, questions, approvals and transport behavior. Concurrent delivery or stale run writes cannot erase acknowledgement or other requests. A later new change is independently open. An agent's acknowledgement is a claim, not proof it understood or fully implemented my request.

7. If an old submission remains protected as in progress, status and any refusal it causes identify that request, its text and original chat. They tell me to check that chat and type the request there if absent, rather than promise that retrying pdd will clear it. Protection never causes an automatic resend, even after time passes or the sender's PID is reused or host name changes.

## Rules to check

- Only a delivered change in the current active run can gain its first acknowledgement; forbidden results include acknowledging an answer, another run's request or an uncertain submission.
- First durable acknowledgement wins. Repetition and concurrency cannot replace its time or note; zero is a present acknowledgement time.
- Visibility is read-only. Warnings cannot block completion, approve a gate, advance an area or infer uptake from transport or summaries.
- Use the existing authoritative delivery journal and its short claim. No second acknowledgement store, long transport claim or extra gate is introduced.
