# Resume work for due run and claim time rules

As a maintainer, I can have Autopilot wake the idle agent for a stalled run or an idle working claim without waiting for a GitHub change.

Draft for review. This is a dependency of [review wakes](autopilot-review-wake.md); both are in scope for this draft.

## Acceptance criteria

1. A local active run with no progress for 60 minutes and an eligible trusted `pdd:working` claim idle for 60 minutes each offer one reason to the idle agent, without a model call in the tick. A claim remains marked claimed. Before the threshold neither wakes the agent.
2. An unchanged delivered time event stays quiet, including after restart; new activity can become due after another 60 minutes. Busy or failed delivery leaves it pending, and current facts are reassessed before delivery so refreshed or ended events are not sent stale. Due reasons can be delivered together with trusted work.
3. Run progress uses this repository's active run status file modification time in the Git common directory. Completed, cancelled, missing, unreadable and other-repository records supply no active progress event. Claim activity uses cached issue update and comment creation/edit times, including label refresh; missing or unreadable activity cannot be due. An unchanged tick makes no extra GitHub query to measure age.
4. Current trust is checked before a due claim is delivered; revoked or stranger text is not forwarded. The skill decides whether to mark a run stuck or inspect takeover. An empty tick with no local progress or usage data stays quiet.

## Rules to check

- Preserve the [launcher time rules and trust boundary](../prompts/cli/autopilot-launcher.prompt.md#tick-and-the-skill-boundary), including one reason line per event and no invented usage reset.
- Check both rules at one millisecond before and at 60 minutes, repeated ticks and restart, and a later activity becoming due. For a claim, check the claimed flag and the takeover reason; for a run, check the stuck reason.
- Check working, blocked and unknown agents defer both events and an idle agent receives them together once. Check failed delivery retries, and activity refreshed while busy cancels the old event until it becomes due again.
- Check cached comment edit time controls claim age without another comment or network query; revoked trust does not send the cached claim. Check real status-file modification times, completed and cancelled runs, another repository, malformed files, and a run ended while pending. Check missing claim activity and an empty tick stay quiet.
