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

After repeated failed validation, inspect the actual failure, identify its cause and change the repair before another permitted check. Do not abandon a useful correction only because two repair rounds failed. Keep the Story's behavior expectations and required validation. One area of an Autopilot run has at most 5 repair rounds: after the 5th, pdd refuses another round; take the stuck path (step 8). A round is a return to an earlier step that clears later steps; a retry after a failed PR open, claim check or push is not one. After the refusal, pdd marks the run stuck and refuses every later `done` of it. Do not resend an unchanged failed check or an external action with an unknown outcome. If the issue is genuinely blocked, record the cause and next action, preserve its claim and progress, and continue with other proven-eligible work. Release capacity only after positive worker-end evidence.

## Alerts

Alert a person only for a real human need or an operational incident: an AI account usage limit (give the reset time when known), a CPU, memory or disk failure, an access or spending decision, an unresolved product choice, or an issue stuck after its retry time. Do not alert for routine progress or for a question that your best judgment settles. Put the question on the GitHub issue, so the answer stays with the original run. In the run, use `pdd workflow ask`; relay the trusted answer from the issue with `pdd workflow changes`. Do not create another run to carry the answer. Then send one alert with the cause, what you tried and the exact help needed:

```sh
pdd autopilot alert --issue N --kind usage-limit|resource|runtime|runtime-access|access|decision|stuck|long-running --input - <<'PDD_ALERT'
{"cause":"...","tried":"...","need":"..."}
PDD_ALERT
```

`usage-limit`, `resource`, `runtime` and `runtime-access` are one incident for this repository and machine. The no-AI tick sends the `runtime` and `runtime-access` alerts and their recoveries itself. When it blocks another issue, make the same call with that issue: pdd adds the issue and sends nothing. `access`, `decision`, `stuck` and `long-running` are one incident per issue, so each access or spending decision gets its own alert. While the need lasts, you may repeat the same call on a later tick: pdd sends nothing for a delivered or unconfirmed alert, and sends again one that failed or had no destination. Add `--update` only for a material change or to send the new issue list. When the incident ends, send `--kind recovered` once with `{"cause":"what changed","kind":"KIND"}`. Without a destination, or when delivery fails, pdd records the alert on this machine and `pdd autopilot status` shows it; continue feasible work. Never guess, set, test or clear the destination: the person sets it with `pdd autopilot alerts set`.

## Room, claim and stuck work

4. Work: use the person's configured agent and execution environment. Respect actual provider limits and the person's chosen spending and concurrency settings. Use the repository's own test commands and requirements; no PDD-specific runner pool, free test slot or fixed CPU/memory threshold is required before starting ready work. If an operation cannot run because of an actual resource or service limit, report that operation as waiting or failed and continue unrelated work that can run. Required verification and merge rules still apply. There is no fixed number of runs; `--runs N` sets an optional cap. At most 2 runs change one prompt file; skip a 3rd and take the next free issue.
5. Claim: only Autopilot uses `pdd:working`. A person or a manual session assigns a person instead. To claim, add the `pdd:working` label and one short comment that names this machine and coordinator ID. If coordinators race, the earlier label event wins. Skip an issue with a live claim. The claim keeps Autopilot ownership until it is removed or expires, even while the run is paused. Each launcher tick writes the time as `lastSeen` in its own claim comment. A claim with no `lastSeen` update for 4 hours is expired. The 4 hours count from the claim comment's last GitHub edit, or from its creation before the first update. A claim record without `lastSeen` (as older pdd writes it), a claim comment without the JSON record, or a bare label, is expired after 24 hours with no issue activity. Remove the label when the run ends. Only the owner of the current live claim removes it: read the claim again just before you remove it.
6. Expired claim: a packet item with `expiredClaim`, or `pdd graph` with "Expired claim, last seen", may be taken over. Read the claim again first and never take a live claim. Remove `pdd:working`, add it again at once (within 10 minutes), and write one claim comment: say why (old coordinator, machine and last seen time) and give the new labelEventId. Put `"lastSeen": ""` in its record, as in a new claim; the launcher tick writes the time. Continue from the saved branch and open PR, not from zero: read them, start the workflow with `--base` set to the open PR's branch, and do not redo finished steps. Keep old comments, branches and PRs as history. After 3 takeovers of one issue, do not take it over again: its packet item has no `expiredClaim`, `pdd graph` shows "Taken over 3 times", pdd refuses a 4th start, and the tick sends one `takeover-limit` rule. Take the stuck path (step 8); keep the claim and progress. Only one coordinator gets the rule. Read the issue again first; skip it if it already has `pdd:stuck`. Taking back your own expired claim (same coordinator ID and machine) is not a takeover. The count starts again at 0 when a person removes `pdd:stuck` at the limit, after a normal release, or when a person removes an expired `pdd:working`. When people and coordinators share one GitHub login, pdd cannot tell them apart: a person's cleanup of an expired `pdd:working` followed by an Autopilot claim within 10 minutes counts as a takeover. Removing `pdd:stuck` at the limit always resets the count.
7. Lost claim: when the winning claim of your issue is expired or belongs to another coordinator, pdd refuses start, approve, park, open, yield and the `done` that pushes or opens the PR with "claim ownership". A `done` of a middle step is not checked. Stop work on that issue and do not push to it. Do not remove `pdd:working`, also when your run ends: it belongs to the current claim and its owner. Keep the local work as history.
8. Stuck: no progress (commit, push, comment or PR event) for 60 minutes, or 30M tokens in one PR stage: add the `pdd:stuck` label, write one comment with the cause, and take the next issue. Send one `stuck` alert. After 4 hours stuck, the tick sends a `stuck-claim` rule: try again with a changed approach and remove `pdd:stuck`, or ask in the configured alert channel as above. After the repair or takeover limit, the rule says so: do not retry, do not remove `pdd:stuck`, write no new comment and send no second alert. Only a person lets Autopilot try again. After the repair limit, they remove `pdd:stuck` and `pdd:working`, then run `pdd workflow cancel N` in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count. While the issue keeps `pdd:stuck`, the tick sends no more `lastSeen` updates, so the claim expires 4 hours later and the issue is not claimed forever.
9. Long-running: 24 hours after the claim with no merge, the tick sends one `long-running` rule. Send one informational alert for that issue and keep working; it is not a stop. Use `--kind long-running`. The tick records it in your claim comment, so a later owner of the issue does not send it again.

## Runtime outage

Runtime is the hosted PDD interpreter behind `pdd test`. A Runtime problem stops only the step that needs Runtime.

- A worker reads pdd's own `pdd test` result. A failed check (✗), a refusal that names a file rule, or a step time limit (`took more than N minutes`: make the step smaller) is this issue's work: fix it as usual. A sign-in problem is an access need, also for a Runtime 401 with any error code. For no verdict from the AI service (`no verdict ·` with an AI-service cause such as `graph-provider-failure`), `busy ·`, not run (exit 5), or an outcome that stays unknown after one `pdd test --read BATCH` (exit 3), ask no person and add no question. Run `pdd workflow park --runtime --reason "<pdd's cause line>"` in the run worktree, then end the turn. pdd refuses the park when the result is the issue's own work or a sign-in problem.
- The run then waits for Runtime with its claim, branch, worktree and progress. After its turn ends, the coordinator may yield its slot by the rule above and fill the slot with other eligible work. The tick watches every waiting run, and each wait ends in a wake or in a `runtime-stuck` rule, so an idle-claim rule for a waiting run needs no action. Follow each `runtime-stuck` rule with the stuck rule.
- During an outage the packet has `runtime` (`unavailable` or `testing`). Only a failed health check opens an outage; waits of several issues while Runtime is healthy are issue problems, and each gets one retry. With `runtime` state `access`, this machine cannot read the Runtime health check (sign-in or `PDD_RUNTIME_URL`): the tick sent one `runtime-access` alert with the fix, nothing is resent, and after 4 hours each waiting run gets `runtime-stuck`. Keep everything else moving: code, native tests, CI, merges, dependency reviews and claims. New issues may start; their native reproduction and Story drafting go on, and their workers park only at the Runtime check.
- A `runtime-ready` time rule names a waiting run that Autopilot wakes. After an outage, the first one is a test: the others come only after its check reaches a verdict. Wake the runs in packet order (oldest first) as worker room allows: send the rule's quoted text, unchanged, with `pdd workflow changes N`. pdd delivers each wake at most once for each park, so a repeated rule sends nothing. The woken worker runs `pdd test --read BATCH` first. It resends only a check that surely gave no verdict, and never an unknown outcome or a failed check. A `runtime-stuck` rule means that one issue waited again after its one resend while Runtime was healthy, or waited 4 hours with a Runtime access problem: follow the stuck rule.
- A Runtime outage adds no merge path. The [$pdd-merge](../../pdd-merge/SKILL.md) rule stays: PR 1 with a fresh checker PASS but no runtime verdict merges with the `pdd:no-verdict` label. `--max-calls` and strict mode stay.

## Merge conditions

Merge only when all of these are true:
- a fresh checker PASS (pdd-check) is for the current head. A PASS for another head counts only when `git patch-id` of both heads is equal and the full suite is green on the exact current head. A conflict fix or any other change gives a new patch-id and needs a fresh PASS;
- the full suite is green on the exact merge head, for PR 1 and the code PR. Red pair: if PR 1's new native tests are red only for the missing behavior, never merge PR 1 alone. When both PRs have a PASS, set the code PR's base to PR 1's base (`gh pr edit CODE --base BASE`); merge the code PR, which carries PR 1, once the full suite is green on its exact head;
- at least one check ran, and all required checks are green on that head. A missing, pending or failed check: wait, do not merge;
- the repository’s required human reviews are satisfied. Read the applicable repository review requirements and `gh pr view PR --json reviewDecision,reviewRequests,latestReviews` before merging. If requirements or review status are unknown or pending, wait and continue other eligible work; do not rely on merge rejection to discover them;
- a second fresh checker agreed when pdd-check asks for one (risk 4-5, a split verdict, or a change to check, merge or approval code);
- no question to a person is open.

After a base change, and right before each merge, run `pdd workflow status N`: pdd refreshes the top of both PRs (status line, checks and merge order).


## Outcomes and retries

Outcomes: merged, dropped, stuck, or one question. Retry a call at most 3 times, only for HTTP 408, 429, 5xx or a network error. Never send a failed check again. Keep `--max-calls` and strict mode. Write each decision on the issue or PR. After a restart, read the issue and PR first and do not redo finished steps.
