# Autopilot delivery

As a maintainer, I can trust Autopilot to keep work until its coordinator can safely receive it, so a startup or dialog cannot lose the work or send it to the wrong place.

## Acceptance criteria

1. A new coordinator starts empty once; recipe and issue work remain pending until the exact coordinator is ready for safe submission.
2. Only an idle or done coordinator receives a guarded packet; working, blocked, unknown, dialog and unreadable states leave work pending.
3. A failed launch, changed target or confirmed rejection consumes no pending recipe, issue, timer or review work. An uncertain submission is retained without blind resend or invented acknowledgement.
4. Acknowledged submission records the delivered work once; it does not claim the agent took it up. Unchanged work stays quiet.
5. Pending work survives coordinator workspace or pane recreation in the dedicated session.
6. The coordinator and issue handoff consistently use the bundled PDD command and explicitly selected HOME/profile, preserving a confirmed saved family. Normal PDD workflow starts or is reused before issue edits or delegation.

## Rules to check

- Launch acceptance alone must not mark the recipe delivered or record an issue fingerprint. A later safe submission must still carry the pending work.
- Readiness and submission apply to the original coordinator; a replacement cannot receive the old packet without a new safe decision. A dialog or unreadable screen must never receive a packet.
- Only confirmed acknowledgement records delivery. A confirmed rejection leaves work retryable; uncertain custody must not be treated as either a confirmed rejection or acknowledgement.
- Starting or reusing the normal workflow precedes issue edits and delegation. Do not switch provider, global account, trust or credentials as a side effect.
