# Share a local runtime limit

I can run several local agents without exceeding my shared runtime limit.

## Acceptance criteria

1. Ten parallel local checks with PDD_MAX_JOBS=3 all finish with at most 3 runtime jobs active at once.
2. Checks, remote lint and Try setup share the same limit across repositories and worktrees; the default limit is 4.
3. A dead process does not free a slot while its runtime job still runs; confirmed completion or 30 minutes allows reclamation.
4. An interrupted or timed-out command retains reservations for unfinished or uncertain dispatched jobs, and releases jobs confirmed ended.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch. Expected cases below come from DESIGN section 4 and E 1, before implementation.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-local-slots.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
