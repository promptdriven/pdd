# Keep my workflow change request while a chat starts

I can request changes immediately after approving an area and trust pdd to wait briefly for the new chat, or keep my one-line request and show me how to retry.

## Acceptance criteria

1. Immediately after `pdd workflow approve 2` starts the prompt-pr chat, `pdd workflow changes 2 "Add the retry example"` waits within the chat's 30-second startup window and submits that request once when the original chat is ready. A chat ready for input has known status idle, working or done; blocked means answer its dialog, and an unknown status never proves readiness.
2. If the chat never becomes ready, pdd stops waiting within the original startup deadline, says it is still starting, keeps the request durably, and shows brief wait/open advice followed by one clearly quoted retry command. Retrying or changing the clock does not extend the wait. A genuinely stopped old chat still says "The prompt-pr chat is not running".
3. Retrying the same pending request sends it once. Different pending requests for the same target keep their order, and acknowledged requests are never replayed. Identical overlapping commands share one request; retrying after the other command delivered it reports that delivery without sending again. An ordinary identical request after acknowledgement is new when no overlapping retry is owed.
4. A blocked or unavailable chat keeps the request and shows an actionable recovery step. An uncertain submission stays visible and is never automatically resent, including when I repeat that text; it does not stop a later new request, and pdd tells me to check the original chat.
5. Requests keep today's one-line behavior: whitespace collapses and trims, while quote characters stay intact. A request submitted while the agent works reaches the same ready chat once without waiting for its current turn to finish.
6. Changes keep approval gates open, answers retain their existing meaning, and delivery neither approves nor advances an area, restarts an agent, nor overwrites progress or newer questions saved while it waits. Other workflow commands cannot undo saved delivery and cause it to be sent again.
7. If a sending command is interrupted or crashes, later commands can recover its abandoned claim without disturbing a live sender. A request whose submission might have happened is kept as uncertain; a definitely-unsent request remains retryable.
8. If the new area's chat record has not appeared yet, pdd keeps my request for that area and waits boundedly for it, or tells me clearly how to open/check the area and retry. It never redirects a request bound to an earlier pane or another area.

## Rules to check

- The startup deadline is 30 seconds after the latest start or resume, capped by the original elapsed budget. At or after the deadline, a missing old agent is reported promptly. Unknown or missing status may wait within that window, but never counts as ready. Inspection failures other than confirmed absence are reported promptly.
- Save custody before transport; a failed save sends nothing. Request state lives separately from ordinary workflow progress, so even an older status, step or question update cannot turn delivered back into pending. Existing saved request state is migrated once; later stale copies are ignored.
- A pending retry shares its accepted identity. An identical overlapping caller promised a retry leaves one coalesced retry receipt; the first identical command after acknowledgement consumes it without sending. A further identical request is new. This gives the promised retry priority when an intentional repeat is indistinguishable. Uncertain requests are retained and skipped for later new work, never replayed; a definitely-unsent earlier failure still holds later pending work for that target.
- Only confirmed dead or mismatched process identities permit claim recovery. PID reuse is not ownership. A live, unknown or malformed claim is never removed by age alone. Interrupt, termination and hangup release only the interrupted command's own claim. Submission uncertainty survives claim recovery.
- A request accepted before its area's chat record has a 30-second window from first acceptance and binds once to that same area's chat, capped by the remaining window. Retry never extends it. A changed area or pane keeps the earlier request and gives an actionable message.
- Submission acknowledgement is not proof that an agent acted on the request. Native waiting-stub evidence checks consumption; actual Codex/Claude turn semantics need separate evidence.
