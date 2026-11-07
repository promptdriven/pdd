# PDD issue handoff

Required step for pdd-autopilot. After readiness and claim, check `pdd workflow status N`.
Reuse an active run with `pdd workflow open N`; otherwise start
`pdd workflow run bug|feature|small-change N --agent AGENT` with the matching workflow
and the packet's agent, or the current agent without a packet. Use the normal PDD
session before issue edits or delegation. The run owns its worktree, area chats,
gates and PRs; do not create issue worktrees or PRs outside it.

The person’s explicit choice of auto and start establishes the chosen automatic work
and merge scope; configuration alone does not. Preserve the person’s actual words or
commands and attribution, without presenting a coordinator summary as a quotation.
The coordinator gives the owner the actual attributed operator action or exact standing
delegation and repo, work and merge scope in the existing owner handoff. Before finishing
the first area, the owner records that same authority and scope in the existing run notes
(`<run folder>/STEP.md`) and directs later area chats to read those notes. On reuse,
carry forward the existing notes. Do not invent words or infer authority from mode.

With a launcher `workflow` packet, use its absolute `pddBin` for PDD commands.
Bind HOME to `home`. If `configHome` is present, bind its `variable` to `path`,
or unset that variable when the path is null. Shell-quote paths. Apply these
bindings to workflow commands and ensure supported workflow routes inherit the
selected explicit profile for new chats. Without a packet, use installed pdd and the current
profile. These command bindings do not alone prove that a default-home profile
reaches issue chats in an existing normal PDD server.

After an automatic PDD run reaches `waiting`, `paused`, `stuck`, `question`,
`completed` or `cancelled`, and its current worker turn is positively confirmed
complete, the coordinator may run `pdd workflow yield ISSUE`. A native Herdr
`DONE` for the matching observed session confirms the turn even when the pane
remains registered. Confirmed absence with ended or failed evidence also
confirms it.
`DONE` alone does not end the PDD run or release its issue claim. Waiting work
keeps its issue allocation and claim. Completed or cancelled work releases its
allocation before the completion request. Running or unconfirmed work does not
yield.

For ordinary recoverable questions, use best judgment, record why, and continue. The explicit Auto-and-start authority also covers routine non-strict workflow approvals through the existing native approval route; it is not checker evidence or a human reply. Keep strict approval and repository-required human reviews. A genuinely blocked issue keeps its claim and history while independent eligible work proceeds.

After repeated failed validation, inspect the actual failure, identify its cause and change the repair before another permitted check. Do not abandon a useful correction only because two repair rounds failed. Keep the Story's behavior expectations and required validation. Do not resend an unchanged failed check or an external action with an unknown outcome. If the issue is genuinely blocked, record the cause and next action, preserve its claim and progress, and continue with other proven-eligible work. Release capacity only after positive worker-end evidence.

For an operational incident or a real human decision, use an existing configured notification integration only when it supports sending and readback. Keep the affected repo and issue, cause, attempted action and exact help needed with the original run. Use `pdd workflow ask` and `pdd workflow changes` to keep the question and its answer with that run. If no supported delivery route exists, record this in the run and continue feasible work; do not guess a destination, repeat an unchanged alert each tick or create another run to carry the answer. Send a recovery update when the incident materially changes or ends.

## Room, claim and stuck work

4. Work: use the person's configured agent and execution environment. Respect actual provider limits and the person's chosen spending and concurrency settings. Use the repository's own test commands and requirements; no PDD-specific runner pool, free test slot or fixed CPU/memory threshold is required before starting ready work. If an operation cannot run because of an actual resource or service limit, report that operation as waiting or failed and continue unrelated work that can run. Required verification and merge rules still apply. There is no fixed number of runs; `--runs N` sets an optional cap. At most 2 runs change one prompt file; skip a 3rd and take the next free issue.
5. Claim: only Autopilot uses `pdd:working`. A person or a manual session assigns a person instead. To claim, add the `pdd:working` label and one short comment that names this machine and coordinator ID. If coordinators race, the earlier label event wins. Skip an issue with a live claim. The claim keeps Autopilot ownership until it is removed or expires, even while the run is paused. Each launcher tick writes the time as `lastSeen` in its own claim comment. A claim with no `lastSeen` update for 4 hours is expired. The 4 hours count from the claim comment's last GitHub edit, or from its creation before the first update. A claim comment without the JSON record, or a bare label, is expired after 24 hours with no issue activity. Remove the label when the run ends. Only the owner of the current live claim removes it: read the claim again just before you remove it.
6. Expired claim: a packet item with `expiredClaim`, or `pdd graph` with "Expired claim, last seen", may be taken over. Read the claim again first and never take a live claim. Remove `pdd:working`, add it again, and write one claim comment: say why (old coordinator, machine and last seen time) and give the new labelEventId. Do not write `lastSeen`; the launcher tick adds it. Continue from the saved branch and open PR, not from zero: read them, start the workflow with `--base` set to the open PR's branch, and do not redo finished steps. Keep old comments, branches and PRs as history.
7. Lost claim: when the winning claim of your issue is expired or belongs to another coordinator, pdd refuses start, approve, park, open, yield and the `done` that pushes or opens the PR with "claim ownership". A `done` of a middle step is not checked. Stop work on that issue and do not push to it. Do not remove `pdd:working`, also when your run ends: it belongs to the current claim and its owner. Keep the local work as history.
8. Stuck: no progress (commit, push, comment or PR event) for 60 minutes, or 30M tokens in one PR stage: add the `pdd:stuck` label, write one comment with the cause, and take the next issue. After 4 hours stuck, the tick sends a `stuck-claim` rule: try again with a changed approach and remove `pdd:stuck`, or ask in the configured alert channel as above. While the issue keeps `pdd:stuck`, the tick sends no more `lastSeen` updates, so the claim expires 4 hours later and the issue is not claimed forever.

## Merge conditions

Merge only when all of these are true:
- a fresh checker PASS (pdd-check) is for the current head. A PASS for another head counts only when `git patch-id` of both heads is equal and the full suite is green on the exact current head. A conflict fix or any other change gives a new patch-id and needs a fresh PASS;
- the full suite is green on the exact merge head, for PR 1 and the code PR. Red pair: if PR 1's new native tests are red only for the missing behavior, never merge PR 1 alone. When both PRs have a PASS, set the code PR's base to PR 1's base (`gh pr edit CODE --base BASE`); merge the code PR, which carries PR 1, once the full suite is green on its exact head;
- at least one check ran, and all required checks are green on that head. A missing, pending or failed check: wait, do not merge;
- the repository’s required human reviews are satisfied. Read the applicable repository review requirements and `gh pr view PR --json reviewDecision,reviewRequests,latestReviews` before merging. If requirements or review status are unknown or pending, wait and continue other eligible work; do not rely on merge rejection to discover them;
- a second fresh checker agreed when pdd-check asks for one (risk 4-5, a split verdict, or a change to check, merge or approval code);
- no question to a person is open.


## Outcomes and retries

Outcomes: merged, dropped, stuck, or one question. Retry a call at most 3 times, only for HTTP 408, 429, 5xx or a network error. Never send a failed check again. Keep `--max-calls` and strict mode. Write each decision on the issue or PR. After a restart, read the issue and PR first and do not redo finished steps.
