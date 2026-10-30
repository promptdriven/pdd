# Share a local runtime limit

I can run several local agents without exceeding my shared runtime limit.

## Acceptance criteria

1. Ten parallel local checks with PDD_MAX_JOBS=3 all finish with at most 3 runtime jobs active at once.
2. Checks, remote lint and Try setup share an explicit PDD_MAX_JOBS=4 local limit across repositories and worktrees.
3. pdd reuses a dead process's slot only after its runtime jobs are confirmed ended or after 30 minutes.
4. Stopping a command preserves slots for dispatched jobs that have not been confirmed ended.
5. Waiting tickets, active owners and claim locks refresh about every 5 seconds; after 60 seconds without refresh, a reused live process ID cannot keep them alive.
6. SIGHUP and SIGTERM remove my waiting ticket and claim locks, while preserving dispatched jobs whose end is unconfirmed.
7. Checking a dead owner never holds the local claim lock during a runtime read, and repeated checks reuse each job observation for about 15 seconds.

## Rules to check

The [slots prompt](../prompts/cli/runtime-slots.prompt.md) owns local admission; the [client prompt](../prompts/cli/runtime-client.prompt.md) owns deadline, transport, restart and no-replay rules. Never turn missing evidence into permission to dispatch.

Signal checks synchronize with the actual claim/admission boundary before interruption, then verify termination, cleanup and no new dispatch while preserving uncertain leases. Do not depend on a short signal timer winning a race against another short pause.

Replacing my active record with another owner's record, even with the same ID and process ID, must not let my command append a request, refresh it or remove it on release or interruption. Check every ownership field and the complete ordered request list before accepting a known owner's update. Ordinary request append/deduplication, promotion and saved reservation use still work; a separately resolved file connection must keep valid updates refreshing without adopting a foreign replacement.

## Native cases for the code step

[Requirement-derived native cases](../test/runtime-admission/runtime-local-slots.json) cover the normal path, limits, interruption and missing evidence. Run them through the real public commands with fake transport/clock and real temporary local state; process races need separate child processes.

Runtime check: NOT REPLAYED (#2548). The companion native case file records requirement-derived inputs and observations for code-step tests; it is not a prompt-runtime scenario. Real runCheck/runTry depend on native Git/source capture, private state, dispatch claims and process lifecycle without a complete Runtime interface. Injected HTTP/clock replies alone cannot establish this Story. Local exclusion, crash/permission behavior and concurrency need ordinary Node tests and separate processes. No Runtime call or pass is claimed.
