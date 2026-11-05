# Catch up dependency work safely

I can stop and restart Autopilot and keep dependency work in sync.

## Acceptance criteria

1. Off keeps saved graph data readable and queues no automatic analysis or start. Restart and fallback reads catch up from current GitHub.
2. Completing a prerequisite releases the dependency hold; reopening blocks it again. An unchanged tick needs no semantic delivery.
3. Busy or dialog-blocked delivery stays pending. A current remote owner is skipped before execution handoff.
4. A bad event signature queues nothing. A duplicate delivery queues nothing twice, and an old event queues a fresh reread rather than applying its payload state.
5. Event status is disabled by default. Configured, installed and delivery-verified remain distinct; polling does not depend on a verified receiver.

6. A restart recovers a fresh saved pending intent before semantic delivery, without adding an already present edge. Two unchanged ticks of a saved question do not deliver analysis again. Observe can return eligible issue work.

7. After a packet is prepared, a new owner, another coordinator on the same machine, or Off prevents an automatic workflow start. The existing run, claim and chat stay unchanged. The current winning coordinator can start its first eligible work; manual starts and active-run resume keep their current behavior. The existing concurrent-run cap counts starting and unconfirmed slots, allows existing-issue reuse without another slot, and defers an unknown count.

## Rules to check

Off starts nothing. Event payloads cannot overwrite current canonical issue state. Only confirmed delivery advances pending delivery state. Current owner and ordinary scheduler rules still control execution. Synthetic signature replies do not prove HMAC correctness, hook installation or live delivery.

## Native public boundary regression requirements

Replay these cases through ordinary `src/workflow-runner.mjs` module function
`startRun`, with real injected git/gh/Herdr ports and saved-run fixtures. Do not
substitute a launcher tick, a skill assertion or a stubbed permission result.
Use an isolated sandbox, never another team's production issues. Run the same
relevant stale-packet/current-other-owner scenario against old and fixed code.
Old code must fail the expected no-start assertion for the ownership race; a
missing-module crash or other setup failure is not a successful control. Fixed
code must prevent replacement, claim release, allocation and chat.

- Stage an eligible packet and its coordinator context, then add a current other
  winner before startRun. Expect exit 2, zero allocateIssueWorktree/startChat calls,
  and unchanged existing run, claim, chat and worktree.
- Repeat with a different coordinatorId on the same machine. Machine equality
  must not allow replacement or claim release.
- Stage a packet, change mode to Off, then call startRun. Expect no new allocation,
  run, claim release, replacement or chat. Existing open/resume and work may finish.
- Give the current coordinator its exact own winning comment/label event and
  otherwise eligible work. It must pass the check and reach ordinary startup;
  its legitimate claim must not forbid its first run. Keep account/room checks.
- An explicit manual start with no automatic context keeps current replacement
  behavior. An automatic context with missing/unknown identity never falls back
  to manual. A stale automatic start against an active owner leaves that owner's
  saved state and native custody byte-for-byte unchanged.

The Runtime cases call the actual proposed current-check function with current
observations. They do not execute the runner or prove this final call boundary.
These ordinary-start cases must be added to native replay in P2 before claiming
that the stale-packet regression is fixed.

The ordinary-start native replay must also use a configured --runs cap with one
starting/unconfirmed slot, then attempt another issue and observe no allocation
or chat. Repeat with an unknown count (deny), actual existing-issue slot reuse
(no extra slot), and simultaneous local starts under the existing allocation
serialization. Use the existing occupied-slot classification: paused/stuck/question
work yields only with confirmed no occupied worker, never from age or labels.
Unknown slots count. The current saved cap cannot be raised or erased by caller
context. Scope is capped automatic starts in this repository/commonDir; manual
starts stay unchanged. Reuse acquireRunLock with the admission filename, through
current reads/allocation/first durable starting record, and release before chat.
Do not add a second cap/claim service or a separate lock policy. A passing
pure current-check vector does not prove local admission/allocation serialization.
