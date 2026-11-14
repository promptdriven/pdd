# Autopilot core engine

Own `src/autopilot-core.mjs`. It is the small native Autopilot engine that a
repository selects with `autopilot.engine: "core"` in `pdd.json`. One tick takes
ready issues, runs one headless agent job per issue, checks the PR natively and
merges it, or ends that one job with one comment. There is no AI in scheduling, no
Herdr, no coordinator chat and no parking. The [launcher](autopilot-launcher.prompt.md)
owns the timer, the tick lock, the GitHub budget and the issue list; it calls
`tickCore` when the engine is core and returns its result.

The rule behind every decision here: **every failure ends one job**. No job waits
for another job, for a person or for a tool fix. The one exception is a stop that
this engine's own step or a service caused while a PR waits for its checks: that job
keeps its PR and tries the step again after a backoff ([Stop owners](#stop-owners)),
because the issue is fine. Jobs share only the slot count and the GitHub budget. A
person retries an ended issue by removing `pdd:stuck`.

## Settings

`autopilotEngine(config)` returns `core` only when `config.autopilot.engine` is the
string `core`; any other value, or none, is `full`.

`coreSettings(config, packageJson, machine = null)` reads the `autopilot` object of a parsed
`pdd.json` and returns exactly these fields:

| Field | Source and default |
|---|---|
| `engine` | `autopilotEngine(config)` |
| `mode` | `off`, `observe` or `auto`; anything else is `off` |
| `trust` | the nonblank strings of `autopilot.trust`, else `[]` |
| `runs` | the slot count. With `machine` (`{auto, runs}`: the automatic slots from the machine's share and this machine's own `--runs`, from the [machine guard](machine-guard.prompt.md)) it is `slotCount({...machine, repoRuns: autopilot.runs}).slots` (#3231: the share of the real limits, at most 4; `--runs` wins; pdd.json can only lower it); without it a positive safe integer `autopilot.runs`, default 2 |
| `label` | trimmed nonblank opt-in label, for example `pdd:autopilot`, else `null` |
| `quietMinutes` | positive safe integer, default 45: the no-progress period (there is no fixed time limit); the tick uses at least 2 timer ticks (`ports.tickMinutes`, default 10), and a core start refuses a value below that |
| `ciStuckMinutes` | positive safe integer, default 360: how long CI may stay pending with no change; at least 3 timer ticks |
| `maxJobHours` | positive safe integer, default 24: the floor of the backstop (see the process rule); no value turns it off |
| `report` | `file`, `draft` or `off`, default `draft`: nothing is posted unless the operator chooses `file` |
| `decisions` | `ask` or `decide`, default `decide` (T10, for the trial on test repositories; the release default comes later): `ask` asks a person ONE question only for a choice that rule 1 allows (a product-direction decision of a feature, or when every reasonable fix breaks something people use today); `decide` asks no choice question, and every choice is listed in the PR. In both, a blocker asks (rule 1, Needs a person) |
| `runtimeRepo` | `autopilot.reports.runtimeRepo` when it is `OWNER/NAME` (the Runtime report repository), else `null` |
| `runtimeOwner` | `autopilot.reports.runtimeOwner` when it is a GitHub login (letters, digits and single inner hyphens, at most 39 characters), else `null`: the assignee of a Runtime report in `runtimeRepo` |
| `repairs` | `autopilot.maxRepairs` (the old key `autopilot.repairs` is an alias): safe integer of at least 0, default 6, the safety cap of repairs for one job |
| `testCommand` | nonblank `autopilot.testCommand`; else `npm test` when `packageJson.scripts.test` exists; else `null` |

`readCoreSettings(cwd, fs, machine = null)` applies it to `cwd/pdd.json` and `cwd/package.json`;
an unreadable file counts as absent.

## State

The launcher passes `ports.root`, one folder for this repository on this machine.
It holds `jobs/N.json` (one file per issue in progress), `logs/` (job inputs,
logs, exit records and result files), `worktrees/` (`N` for the job branch,
`N-review` and `N-suite` for clean checkouts of the PR head), `history.jsonl`
(one line per finished job: time, issue, outcome, text, PR, log; and strike lines,
below) and `core.json` (the machine pause and the pending no-result). The job file and the GitHub labels are the whole state; a
restart reads them again. A job file has `issue`, `title`, `url`, `body`,
`branch`, `worktree`, `claim {commentId, labelEventId, lastSeen}`, `phase`
(`running`, `pr` or `ending`), `role` (`build`, `repair` or `conflict`), `repairs`, `started`,
`progress {sig, at, running}`, the started `agent` job, and in phase `pr` also `pr`,
`head`, `runtime`, `review` and `suite`.

**The process rule (debate C, one function `watchProcess`).** It applies to every agent
process: build, repair, conflict, review and suite, and to the `pdd test` run of the
Runtime step (role `runtime`, like the suite: no P1, P2 or P3). Each tick, for each running process:

- **T1 "something new".** The process makes progress when one of these is new to it (a
  16-hex SHA-256 prefix that is not in its seen set, the file `LOG.seen`): (P1) the commit
  at HEAD; (P2) the worktree state: HEAD, `git status --porcelain=v1
  --untracked-files=all`, `git diff HEAD` and each new file with its content hash (files up
  to 1 MB; the size only above), so a re-run that writes the same file or an edit that flips
  back is not new; (P3) a tool call in its own stream that is not a wait (Codex `--json`
  `item.completed` with its type and fields; Claude `stream-json` `tool_use` with its name and
  input; agy `stream-json` `step_update` of `step_type` `tool` and `state` `DONE` with its
  `tool_name` and `tool_info.parameters`; the tools `wait`, `wait_5_seconds`, `wait_agent`,
  `sleep`, `list_agents`, a `write_stdin` with no input and a `sleep N` command are waits);
  (P4) a tool output line (also of a wait) or a
  plain log line, after normalization: dates, clock times and durations removed; UUIDs, hex
  ids of 7 or more characters and 20 or more base64 characters with a digit and a letter
  become `X`; temp paths become `T`; digits become `N`; spaces trimmed; (P5) 10 s or more of
  CPU time since the last tick in the process's children (`ports.jobs.cpu`, by pid, without
  the wrapper and the agent CLI). The log size, prose, reasoning and token counts are never
  new. The reviewer and the suite have no P1 and P2; the suite has no P3 (its log lines are
  P4). Each tick reads only the new whole lines after a saved offset (at most 8 MB). The
  first look sets the baseline (the clock keeps the process start); a sleep gap restarts
  the clock, and the part of a shorter tick gap beyond one timer interval (`ctx.tickGap`)
  moves the clock forward (a short sleep or a late timer is not quiet time). A suite that
  waits in the machine's suite queue is never quiet (like a CI wait): from a log line that
  starts with "waiting for a check slot" until the line "running the full test suite" (the
  queue admitted it), each tick counts as new. Only the queue time is exempt: before the
  queue (`npm ci`, the start of the suite command) and after the admission, T1 applies as
  usual. The note and the backstop count from the process start. **End:** nothing new for `quietMinutes` (at least 2 ticks) stops the process.
  Before every stop, save the job and use the headless job runner cleanup. That cleanup
  owns its fresh live-process capture and any stop; a separate status read or snapshot
  is not cleanup proof. A quiet retry or a replacement for a new head starts only after
  cleanup confirms every saved identity is gone. If it cannot confirm, retain the old
  part record and retry cleanup on a later tick. The same proof is required before a
  repair, conflict update, base refresh or mechanical head change clears a saved part.
  Build, repair or conflict with no valid result: `no-result` ("the ROLE agent made nothing
  new for N minutes (no new commit, file state, tool call, output line or CPU use)"). A
  reviewer: no verdict (one retry, then `no-result`). A suite: a runner failure, started
  again at most twice; nothing new on all 3 tries (or deaths and quiet ends together 3
  times) is `no-result`, never `pdd` / `suite-broken`. A quiet suite can also be a hang
  of the change, and every such stop has one owner: see [Stop owners](#stop-owners).
- **The note** (alert only): at `noteHours` = 3 h of process age, one `long-running` alert
  per process with the issue, the role, the age, the new commits, file states and stream
  items of the last hour, the log name and "This job goes on … To stop it, remove
  pdd:working or add pdd:stuck."
- **The backstop:** the process age is the time since its own start (`started`) minus the
  sleep gaps of this machine (`job.gaps`); nothing resets it (no line, commit, file, CI
  change or lane wait). The limit is max(`maxJobHours`, 4 × L), where L is the longest
  process of the same role that ended with a valid result by itself in this repository on
  this machine in the last 30 days (`durations.jsonl` rows `{at, role, minutes}`; a process
  that T1 or the backstop stopped never counts). At the limit: stop the process, write
  `git status --porcelain` and `git diff HEAD` (redacted) to `logs/ID.partial.log` for a
  worktree process, send one `stuck` alert per process, and end the job as `job` /
  `no-result` with `ceiling: true` ("the ROLE ran N h (its limit: the larger of
  autopilot.maxJobHours and 4 times the longest successful ROLE here, D) with no
  result"). The job file keeps the alert keys (`alerted`).

The build, repair and conflict prompts say: "Do not wait for CI and do not run the full
test suite. Autopilot runs both after you finish." Status shows each running process as
"ROLE AGE; last new thing D ago (new KIND); quiet limit N min; backstop H h (longest
success here D)". `progress {sig, at, running}` mirrors the clock of the running agent.
In phase `pr` the signature
is the head, the CI state and picture (each check's name, state, conclusion and time),
the review and suite states and the reviewer's log; it runs while CI is pending (queued
or in progress, or no check yet within its 10 minutes), the reviewer runs or the suite
process is alive. CI that stays pending with no change of its picture for
`ciStuckMinutes` ends the job with `job` / `checks-stuck` under the no-result rules
(named pending checks; a cause with `noResult` follows them like `no-result`) as a
`service` stop: CI never started, so it is not counted for the issue. A new job, a repair, a PR result and a base
refresh start the clock again.

Slots come only from these job files, never from workflow allocation or other
local records. A job holds a slot while its process runs or its outcome is not yet
handled (phase `running` or `pr`), except a job whose Runtime step waits for the
interpreter maintenance (merge check step 5a): it runs no process, so it holds no
slot and other jobs go on. A job in phase `ending` has its outcome decided
and only finishes its GitHub writes, so it holds no slot. Each tick advances every
job before intake, so a job whose process died, for example after a restart, is
ended or moved to the merge check before free slots are counted.

## Tick

`tickCore({state, settings, budget}, ports)` returns `{exitCode: 0, message}`.
`state` is the launcher state (`cwd`, `repo`, `coordinatorId`, `machine`,
`baseBranch`, `agent`, `packageRoot`). Steps, in order:

1. Mode `off` returns `Autopilot is off.` Then read `core.json` and save `lastTick`
   (now). A **sleep gap** is a gap since the saved `lastTick` that is longer than the
   quiet period (a laptop sleep; a clock that went back is no gap). Mode `observe`
   does everything that `auto` does (claim, build, PR, review, suite, CI, Runtime,
   base check, repairs, END) **except the merge** (merge check step 8); its message
   starts `Autopilot core (observe: no merge):`.
2. Read the open issues through `ports.listIssues()`. A failed list skips the
   person checks and intake for this tick; jobs still advance. When any open issue
   without `pdd:working` or a local job carries `pdd:would-merge`, read
   `repos/REPO/pulls?state=all&base=BASE&per_page=30` once and, for each such issue whose
   latest repository PR (head branch `pdd/core-N-*`) is merged into `baseBranch`, read its
   timeline, remove `pdd:would-merge` and (unless the issue was reopened after that
   `pdd:would-merge` label or that PR body marks the work partial with `Refs`, `Part of` or
   `Not fixed yet:`) close the issue (`state_reason: completed`); a failure only warns.
3. A person stops a job by closing the issue, removing `pdd:working`, adding
   `pdd:stuck` or assigning someone. Then stop its processes and clean up locally,
   with no GitHub write, and do not take that issue again in this tick. A job with a
   PR reads it first: a merged PR (GitHub closes the issue from "Fixes #N") finishes
   as merged, not as a person stop.
4. For each own claim of a job that is not quiet, read the winning claim
   with the owners port first. The job still owns the issue only while the winner is
   this machine's coordinator, machine and claim comment. When the owner is unknown
   because a later claim comment names this job's label event (a loser whose delete
   failed), delete those later comments and read again. When another machine holds
   it live, hand over (below). Else
   heartbeat it through `refreshClaimHeartbeat` of the
   [GitHub dependency reader](issue-dependencies-github.prompt.md). A claim not
   refreshed for 4 hours gets no heartbeat: expiry is final. At the GitHub reserve
   floor (`budget.state` `reserve`) the tick stops after the heartbeats.
   **GitHub share**: every claim read through the owners port that is live (`active`,
   not `expired`) records its `machine` with the time in `core.json` `peers` (kept 4
   hours). The core's budget divides the launcher's `allowed` calls by k, the number
   of machines with live claims on this repository (the saved peers, and this machine
   when it holds a live claim; at least 1), and is `low` when `used` reaches that.
   With a `low` budget no new job starts: intake is held with `intake held: the GitHub
   budget is low (this machine used U of A calls in the last hour, a S% share for k
   machine(s) with live claims)`. Jobs still advance.
5. Advance each job, each in its own error boundary. An error saves `lastError` on
   that job, and `lastErrorTool` true when it came from a GitHub or Git call, and the
   tick continues with the next job. A job that waits with no error clears both, and
   so does a new head. A step wait (below) clears neither. A quiet job whose advance
   fails on 2 ticks is a stop of this engine's own step (owner `service` when the last
   error is a service error, else `pdd`; see [Stop owners](#stop-owners)): in phase
   `running` it ends as a `no-result` release, so no job holds a slot or a claim long
   past its quiet period; in phase `pr` it is a step wait. A
   `running` job with no agent record (the tick died between its two saves) ends at
   once as `no-result`. After a sleep gap nothing could make progress: every job's
   quiet clock starts again (`progress.at` = now). A claim that expired in the gap, or
   an agent whose process ended in the gap with no exit record, is this machine's
   fault, never a timeout or claim-expired END: a **machine no-result**, a release
   with no comment and no `pdd:stuck`, which is not counted for the issue (no
   cooldown, no strike) and does not add to `streak`.

**Hand-over**: a job that lost its claim to another machine stops its processes,
changes nothing on the issue (no comment, no label), marks this machine's own open
PR of that job as draft with one note (one try; a failure only warns) and cleans up
locally with outcome `handed-over`. It never merges.
6. Intake fills free slots (see below).
7. After intake, call `intakeTick(ctx, rows)` of the
   [intake cards](autopilot-intake.prompt.md) inside a try/catch: with
   `settings.intake` `shadow` (the launcher sets it from the machine) and an issue
   list it runs one shadow pass; otherwise it only stops card jobs that still run.
   An error is one warning, and it never changes a start, a slot or the message.

The message counts started, merged and ended jobs and repairs, the busy slots and
any intake hold, for example
`Autopilot core: 1 started, 0 merged, 0 ended, 0 repair(s); 1 of 2 slots busy.`

```mermaid
flowchart TD
    R[ready issue] --> C{claim won?}
    C -->|no| X([skip; no start])
    C -->|yes| B[build job running]
    B -->|result pr| M{merge check}
    B -->|failed, dead, no result, no progress| E([END])
    M -->|all green| G([merge, close issue])
    M -->|waiting| M
    M -->|red, repairs left| P[repair job running]
    P -->|result pr| M
    P -->|failed, dead, no progress| E
    M -->|red, no repairs left; head moved; PR closed; no progress| E
```

## Ready rule

`readyIssues({state, settings}, ports, rows)` returns the issue numbers in intake
order. An issue is ready when all hold: it is an open issue (not a PR); it has no
assignee; it has no `pdd:stuck`, `pdd:needs-decision` or `pdd:would-merge`; it is not cooling down (no `noResult` history
line of the last 24 hours on this machine after the issue's latest `reset` line); it has neither report label (`pdd:runtime`,
`pdd:autopilot-report`: report issues wait for a later self-fix lane); it has the
opt-in label when `label` is set; it is not held (the loop guard of
[Stop owners](#stop-owners)); no
local job holds it; its author is trusted (`ports.trusted(row)`, the launcher's
trust rule); no open issue blocks it; and it has no live `pdd:working` claim by
anyone. Blocking means a GitHub issue dependency (`dependencies/blocked_by`, read
only when the row's dependency summary is not zero) or a body line
`blocked by #N`, `blocked by OWNER/REPO#N` or `blocked by` an issue URL, that
names an open issue, or, for an issue with comments, the hidden marker
`<!-- pdd:core-blocked-by:OWNER/REPO#N:FINGERPRINT -->` in its latest core END
comment when OWNER/REPO#N is open. A labeled issue is ready only when its winning claim, read
with the dependency reader's owners port, is expired and not takeover-limited.
Order is oldest `created_at` first, then the lower number. A read error skips only
that issue for this tick.

## Claim and start

**No label, no claim.** When the settings have `labelRequired` (the launcher sets it) and no `label`, intake claims
nothing and returns `intake held: no opt-in label; run pdd autopilot start --label pdd:autopilot and mark issues with
pdd autopilot add N`. Jobs still advance. Without `labelRequired` (a direct `tickCore` call), no label means every
ready issue.

**Collisions at start (debate B 5.1, 5.2; notes and hints, never a lock).** S2: intake
reads up to the free slots plus 4 ready issues and starts first those whose named
paths (paths in the title and body) meet no other running job (its named paths and its
changed files); else the oldest. A slot is never left idle for it. S3: the build brief
lists each other running job of the repository (this machine's job files; for other
machines the `files` of the claim records of `pdd:working` issues, at most 10, read only
when an issue is ready) with
"Other jobs change these files now. Change them only when the issue needs it. Keep such
edits small and on their own lines.", and the base merges of the last 24 hours that
touched files that the issue names. P1: at each push (once per head) the job's changed
files are written into its claim record (`files`) with a PATCH of its own claim comment.

For each ready issue while slots are free, at most 3 claim attempts per tick:

1. Make the job worktree first, so that a local failure touches no issue. Fetch
   `origin/BASE` once per tick; a fetch failure is not about one issue, so it stops
   intake for this tick. A leftover `worktrees/N` is ours: remove it with
   `git worktree remove -f -f` (this also removes a worktree that Git left locked),
   then the folder, then `git worktree prune`. If it still exists, or
   `git worktree add -b pdd/core-N-STAMP worktrees/N origin/BASE` fails, skip only
   this issue for this tick and go on with the next one. Removal also runs when the
   folder is gone: `git worktree unlock` and `remove -f -f` clear a registration that
   Git still lists, then `prune`. STAMP is the time in base 36
   and a short random part, so a retry of the same issue never meets the kept branch
   of an earlier job. Each job file has a random `id`; each started process has the
   id `N-ROLE-STAMP`.
2. Claim with the shared label and comment rule: read the issue again and give up
   when it is closed, stuck or assigned, or when a claim is live. An expired, not
   takeover-limited `pdd:working` is removed first, but only when a fresh timeline
   read shows that the winning label event is still the expired claim's event: a
   newer event is someone's fresh claim. Add `pdd:working`. The winning label event
   is the first `pdd:working` label event after the last removal. Post one claim
   comment `Autopilot core claim.` with a fenced JSON record
   `{repository, coordinatorId, machine, labelEventId, lastSeen: ""}`, where `machine`
   is this machine's id (`state.machineId`, else `m-` and the first 12 hex digits of
   the SHA-256 of the host name), never the host name. The job saves it as
   `claim.machine` and heartbeats with it. A claim whose record names this machine's
   host name (an older build) or its id is this machine's. The machine
   wins only when its comment is by the winning event's actor and is the earliest
   such comment that names that event, and a read of the winning claim through the
   owners port shows no other live owner. A loser deletes its own comment, removes
   its worktree and starts nothing. Two machines with one GitHub login therefore
   agree on one winner. A claim that fails partway leaves nothing of its own: this
   machine's comment is deleted, and the label is removed only when the winning label
   event is its own: the era it saw after its label POST is still the current era, the
   winner's actor is this machine's login (its comment's author, else `GET user`),
   and no other claim comment names that event. Otherwise (another login, a later era,
   or an error in these reads) the label stays.
3. Prepare the build brief before machine admission, including the collision note and
   the open-issues brief. These local and GitHub reads can be slow. They never hold a
   shared machine admission lock. If the open-issues read fails, retain that failure
   through admission: a denied job uses rollback, while an admitted new build closes
   older PRs and then ends as `no-result` without starting an agent.
4. Immediately before retaining a new slot, call the optional launcher's
   `ports.machine.reserve()`. While its release function is held, read the refreshed
   machine room, refuse a full room, and atomically save the slot-holding job file.
   For a resumed approval PR, save its `pr` job instead. Release the function before
   older-PR cleanup and local process start. That saved record retains the slot
   through those slow operations.
   If admission is busy or the room is full, start no job and attempt to roll back this
   tick's claim and worktree under the claim-owner rule, plus its newly-created branch
   for a new build. A resumed approval job keeps its existing approval branch. If
   GitHub rejects a claim delete, its existing expiration and takeover path handles that
   stale claim on a later tick; this attempt never deletes a later owner's label. A
   crash after the job save but before an agent record leaves a slot-holding job that
   the next tick releases as `no-result`, with its claim and worktree.
5. For a new build after admission and release, close the issue's older core PRs: each
   open PR of this repository (not a fork) whose head branch starts with
   `pdd/core-N-` and is not the new branch, and that is not merged, gets
   `state: closed` and one short note with the marker
   `<!-- pdd:autopilot-core:superseded:N:BRANCH -->`; its branch stays. A PR from
   another branch prefix, or one with a `would-merge` or `needs-approval` note by this
   engine's own login (observe mode validated it, or it waits for a person), is never
   touched. A failure only warns. Start the local build process after that cleanup. A
   start error, also one that the spawn reports later, ends the saved job as
   `no-result`; it never stops the tick.

Intake is held before a claim when the saved agent is not Codex, Claude or agy, when
`ports.agentReady()` is false at the first ready issue (for example a Codex usage
limit), while a machine pause runs (below), or while CI does not start in this
repository ([Stop owners](#stop-owners), #3260). A final machine-room denial can
occur after this tick made a worktree and claim; it leaves no admitted job and uses
the owner-safe rollback above. The room is `ports.machine.room` (the
[machine guard](machine-guard.prompt.md)'s `machineRoom` for Autopilot's share of
the whole machine). Immediately before it saves a new slot-holding job, the core
calls the optional launcher's `ports.machine.reserve()`. It returns a release
function after refreshing the shared guard while holding the machine admission lock,
or null after its bounded wait. The core holds that function only through the room
check and atomic job save, then calls it before older-PR cleanup, process start, any
END or other cleanup. The saved job retains the admitted slot while those later
operations run. It does not reserve around issue scans, worktree preparation, claim
and other GitHub reads, build-brief preparation, heartbeats, merge checks, reports
or running-job work. A null reservation holds intake with
`intake held: the machine admission is busy; the next tick retries.` The tick message then says
`intake held: REASON`, for example `intake held: 4 of 4 Autopilot jobs on this machine
run (all repositories, 50% share)`. With room, intake claims at most `room.free` issues,
the jobs that the machine's share still allows. `busySlots(root, fs)` (exported) is the
number of slot-holding jobs in one core folder; the launcher sums it. Running work goes
on; the room check never stops a job and never counts as no progress.

**No result is a machine fault first.** An agent that exited with no result, a start
failure (also one that the spawn reports later), a dead process (a restart or a
sleep), a job with no agent record, a quiet job that cannot advance, a quiet agent, a
reviewer that twice gives no valid verdict and a suite runner that died 3 times all
end as `no-result`. Every job kind follows the same rules, in every machine state.

1. A `no-result` end releases the issue: delete this machine's claim comment, remove
   `pdd:working`, post no issue comment and add no label. Close this job's own open PR
   (found by its number, or by its branch through `pulls?state=open&head=OWNER:BRANCH`):
   first set `state: closed`, then post one short note with the marker
   `<!-- pdd:autopilot-core:release:N:JOB-ID -->`; the branch stays. A GitHub error
   leaves the release unfinished, so a later tick tries the close again (the job saves
   `prClosed` when it is done). Record `released` in the history and skip the issue
   for the rest of the tick.
2. Counting. A `no-result` end is **counted** for its issue only when it is the first
   one after a job result on this machine (`streak` was 0). Later ones in the same
   streak are the machine: they only release. A counted end has `noResult: true` in
   its `released` line, so the issue cools down for 24 hours (ready rule). It is also
   saved as `pending {issue, at}` in `core.json`. When the next end on this machine is
   a job result, the pending end fell between results: append the strike line
   `{at, issue, strike: true}` (the time of the no-result). When the next end is
   another `no-result`, the pending end is dropped; no strike. So an outage gives a
   strike only when it ends exactly one job, and a bad issue that fails between
   results gets a strike each time. **An AI-service problem is the agent account, not
   the issue (T08):** a build, repair, conflict or review agent that ended with no result
   because the AI service refused it is never counted: no cooldown, no `pending`, no
   strike. It adds 1 to `streak` like every `no-result` (the machine pause below). Its
   text names the service message: "the ROLE agent exited with CODE with no result: the
   AI service said "MESSAGE" (an agent account or service problem, not this issue)". The
   message comes from the last 64 KB of the agent log: the last error event (Codex
   `{"type":"error"}` or `turn.failed`, Claude a `result` with `is_error`, any JSON with
   an `error` message) in its last 40 lines, or one of its last 5 plain lines, when it
   has the shape of a provider message, not a single word: "model is at capacity",
   "out of credits", "credit balance is too low", "insufficient quota" or "exceeded your
   current quota", "hit your usage limit" or "usage limit reached", "rate limit
   exceeded" or `rate_limit_error`, "too many requests", `overloaded_error`, "not logged
   in", "please run /login" or "please log in", "invalid API key" or
   `authentication_error`, or a status shape for 401, 429 or any 5xx ("API Error: 529",
   "HTTP 501 Not Implemented", "HTTP 520", "status 429", "401 Unauthorized", "503 Service
   Unavailable"). A terminal error event (the Codex error or `turn.failed`, the Claude
   `result` with `is_error`) also counts with a clear account or service refusal shape:
   "out of credits", "SERVICE is at capacity" or "SERVICE overloaded" (SERVICE one of
   service, server, model, provider, API), a message that starts with "sign-in required",
   "login required" or "authentication required", or "quota exceeded". A message that
   reads like a test diagnostic (it names a test, an assertion, an expected value, a
   fixture or a spec) is never a service problem, in any shape. An ordinary error line,
   plain or in an event (for example "login test failed", "rate limit test failed:
   expected 3 requests, got 2" or "quota of 3 items exceeded in the fixture"), keeps its
   strike. A counted end of an issue with 2 strikes in the last 7 days is a normal
   END: one comment and `pdd:stuck`. Nothing else marks an issue stuck for no result.
   A stop with an owner ([Stop owners](#stop-owners)) changes this counting: `machine`
   is counted only for the cooldown (no `pending`, so never a strike or an END);
   `service` and `pdd` are never counted; `issue` writes its strike at once.
   Each `ended` line has `reset: true`: the cooldown and the strikes read only the
   issue's lines after its latest reset, so a person's retry starts fresh.
3. Machine pause, saved in `core.json` as `streak`, `hours` (the next pause length),
   `pausedUntil` and `pausedHours`. Each `no-result` end adds 1 to `streak`. When no
   pause runs and `streak` is 3 or more, no new job starts for `hours` hours (1, then 2,
   4 and 8 at most) and one `usage-limit` alert goes out through `ports.alert` with
   `update` and the text "Autopilot paused new jobs for H h: the agent ended N jobs with
   no result. Check sign-in and limits." (the machine and the end time follow; when the
   end that starts the pause is an AI-service problem, the text also has `The agent
   said: "MESSAGE".`, so the alert names the account state). When
   the pause ends, intake goes on as usual. Any job result (a build or repair PR or
   reported failure, a valid review verdict, a merge) sets `streak` to 0 and `hours`
   to 1. Jobs that already run always go on. Unknown or broken saved state (a missing,
   `null`, non-object or non-JSON file, a pause end that is not within its length
   from now, for example after the clock went back, or a `pending` that is not
   `{issue, at}` numbers) reads as not paused, `streak` 0, `hours` 1, no pending; it
   never stops a tick or status.
4. `history.jsonl` is read line by line and a line that does not parse is skipped.
   Before each append, the file gets a newline when it does not end with one, so a cut
   line never swallows the next record.

## Stop owners

A1 of #3238: a stop where the time ran out (a process that T1 stopped, a quiet merge
check, a job that cannot advance, CI that stays pending) must not blame the issue for a
fault of Autopilot, a service or the machine, and a person must see on the issue when
the change itself is the cause. The engine knows what ran when the time ran out: its
own step, a service wait, the agent, or a command of the agent. One function gives
each such stop one **owner**, with the owner words of the report routing. The owner is
saved as `owner` in the end cause, in the history line of the outcome and in the
strike line, and status shows it.

| Owner | The stop | Strike | Action | Note on the issue |
|---|---|---|---|---|
| `pdd` | a merge check step of this engine is quiet and its last error is not a service error: the base check could not verify (code `base-check`), a GitHub or Git call, a refused `gh pr merge` or an unconfirmed claim (`merge-check-tool`, `claim-error`), or no error (`step-quiet`); also an advance that throws on 2 quiet ticks (`crash`; in phase `pr`, `merge-check-tool` for a GitHub or Git error) | no | one report (below); a **step wait** in phase `pr`, a release that is not counted in phase `running`; `streak` + 1; never an END | no |
| `service` | the same stops when the last error is a service error (a GitHub status 429 or 5xx, no reply, a time-out, a network error, a rate limit); an agent whose log names an AI-service problem (T08); CI pending with no change for `ciStuckMinutes`; CI that GitHub does not start (#3260, below) | no | no report; a step wait in phase `pr` (no `streak` count); CI that does not start: the job waits and intake holds; else a release that is not counted, `streak` + 1 | no |
| `machine` | a build, repair or conflict agent that T1 stopped, with no repeated hang; a reviewer that ends with no verdict after a T1 stop; a suite run that ended with no result (it died, or died and went quiet, 3 times); a sleep gap | no | a release; `streak` + 1; when `streak` was 0 the issue cools down for 24 hours, with no `pending` | no |
| `issue` | the same command hangs again at this head (two hang records of the agent with the same command at the same worktree HEAD, then a T1 stop or an exit with no result), or the full suite is quiet twice at one head, or once in a test file that the PR changes | yes | the issue stop (below); the 3rd strike in 7 days is the END | yes |

**Hang records.** Agent jobs (build, repair, conflict, review) start with the
wrapper's hung-command watch (`hung: {after: 15 min, every: 30 s, cpu: 2}`, the
[headless job runner](agent-job.prompt.md)): the wrapper stops a command that makes no
output and almost no CPU for 15 minutes, and the agent goes on. Each tick, for a
running build, repair or conflict agent, the core reads `ports.jobs.hangs(part)`
(native `agentJobHangs`) and saves each new record (by its `at`) in `job.hangs` (the
last 20) as `{at, part, role, command, shown, minutes, last, test, head}`: `part` is the
process id, `head` the record's own `head`, else the HEAD of the job worktree at that
read, `shown` the command a person typed (the text
after `-c` of a shell, or the text of Claude's `eval '…'`, at most 120 characters),
and `test` the last test file that the command or the last line names (a path with
`test` or `spec` and a `.js`, `.mjs`, `.cjs`, `.ts` or `.py` end). Two records with the
same command after the output normalization of T1 (P4) and the same head are a
**repeated hang**. A quiet suite gives a record too: `command` is the test command,
`minutes` the quiet period, `last` the last nonblank line of its log and `test` the last
test file named in its last 40 lines.

**The step wait** (owner `pdd` or `service` in phase `pr`): stop the checks, leave the
merge lane (the PR enters it again after the wait), save
`stepStop {owner, code, text, head, count, at, until, report}` and set the quiet clock
to `until` (`progress.at = until`): the job keeps its PR, claim, heartbeat and slot,
and it is not quiet while it waits. The wait is 15 minutes × 2^(count − 1), at most 8
hours (15, 30, 60, 120, 240, 480 minutes); `count` starts again at 1 for a new head.
Until `until` the merge check does not run (person stops and heartbeats still do);
then it runs as usual. Only owner `pdd` files the report and adds 1 to `streak`, so
repeats of the same fault pause intake (the machine pause). The report goes through
the [report owner](autopilot-reports.prompt.md) with the repository's settings and
the cause `{kind: pdd, component: autopilot-core, code, text, stopped: true}`; each
stop files or counts it, and the dedup keeps one report. A merged PR still finishes as
merged at the next merge check, also after a wait. A person ends the wait by removing
`pdd:working`.

**CI that does not start** (#3260). In a person's private repository GitHub Actions can
stop starting runs (the account's Actions minutes or spending limit). In the CI read
of the merge check: CI is pending, no check run is in progress, and the CI picture
of the head has not changed for 20 minutes, and either a check run is `queued`, or
there is no check run and a workflow run for the head (`actions/runs?head_sha=HEAD`,
status queued, waiting, pending or requested; at most 3 runs) has no job in progress
or completed (`actions/runs/ID/jobs`); or every failed check of the head failed with a
billing or spending-limit message (its output title or summary, else its annotations:
"spending limit", "billing", "account payments have failed", "account is locked",
"Actions minutes", "minutes quota" or "limit", "job was not started"). Then the CI
state stays `pending` with `notStarted {reason: queued | billing, since}`: no red, no
repair, no strike, no END, no issue note, and no `ciStuckMinutes` release (the job
waits; the merge rule for this case is a later decision). The first such read of an
outage saves `ciDown {since, reason, message, issue, pr, head, at}` in `core.json` and
sends one `usage-limit` alert: "Autopilot: GitHub Actions does not start runs in this
repository (queued since HH:MM UTC). This is often the account's Actions minutes or
spending limit: Settings → Billing → Actions." (for a billing failure: "GitHub Actions
did not start a run in this repository: GitHub said "MESSAGE". …"). There is no second
alert while `ciDown` stays. While it stays, intake is held with `intake held: TEXT New
jobs start when a CI run starts` and status shows `CI does not start: TEXT New jobs wait
until a CI run starts.` A check run in progress or completed (not a billing failure)
in any CI read clears `ciDown`; when no job read CI in a tick, intake reads the latest
10 workflow runs at most every 10 minutes and clears it when one created after
`since` is in progress or completed with success, neutral or skipped.

**The loop guard** (lead decision, Nov 11): a fault of Autopilot or a service that
never ends must not loop forever on one issue. Each step stop writes the history line
`{at, issue, stop: true, owner, code}`; a release with owner `pdd` or `service` has the
owner in its `released` line. When a stop is the 3rd one owned by `pdd` or `service`
for the same issue in 24 hours (counting after the issue's latest reset and latest
hold release), the engine **holds** the issue: one line `{at, issue, hold: true, owner,
code, text, version}` (version = `ports.version`) and one report (code `stop-loop`,
`stopped: true`), never an END and never a strike; the stop itself still adds 1 to
`streak`. A held job in phase `pr` keeps its PR, claim and slot and runs no merge
check; a released issue is not ready (ready rule). The hold ends with a new engine
version (`ports.version` differs from the saved one), or with a comment on the issue
by a trusted person after the hold (not a claim comment and no `<!-- pdd:` marker).
The issue's comments are read only when the issue changed after the hold, and for a
held job at most every 30 minutes. Then one line `{at, issue, unhold: true, text}`
starts the count again, and a held job gets a fresh quiet clock and runs its merge
check.

**The issue stop** (owner `issue`):
1. Count the issue's strike lines of the last 7 days after its latest reset. With 2 or
   more, this stop is the 3rd: END with `job` / `hung` and the hang text (one END
   comment and `pdd:stuck`, as today).
2. Else append the strike line `{at, issue, strike: true, owner: "issue", hang}`.
3. Post one note on the issue, or update in place (PATCH) the note of this engine's
   login with the marker `<!-- pdd:autopilot-core:stop-note:N -->`: "Autopilot
   stopped a job here: `SHOWN` hung for M minutes[ in TEST] on this change (head
   SHORT). NEXT Nothing to do now." and "Stops caused by this change in the last 7
   days: K of 3 (the 3rd one ends the run with `pdd:stuck`)." NEXT is "A repair starts
   now with that detail." or "It tries again after YYYY-MM-DD HH:MM UTC with that
   detail." (the cooldown end). A failed note write only warns.
4. A job with a PR (the suite, or a repair or conflict agent) gets a repair through
   the repair rules with one red finding that names the command, the minutes, the last
   output line, the test and the head. The strikes decide the END of a hang, so this
   repair compares no findings (the same-finding rule does not apply to it); with no
   repair left (`maxRepairs`) the stop ENDs as `job` / `hung` before step 2. A build with no PR is released and counted for
   the 24-hour cooldown, with no `pending` (the strike is already written) and no
   `streak` count; the next build of the issue gets the hang in its brief ("An earlier
   Autopilot job on this issue stopped: …", from the latest strike line with a hang
   after the latest reset).

A stop owned by `pdd`, `service` or `machine` writes nothing on the issue; status shows
it, and a `pdd` stop files one report.

## Jobs

Every core job uses its disposable checkout path as both cwd and custodyRoot. Build,
repair, conflict and Runtime jobs use the issue's worktree. Review, suite and vector
jobs use their fresh named checkout. This explicit root lets the job runner retain a
late helper that still uses that checkout. A cwd alone is not ownership evidence.
Never pass a shared source root. Intake uses a persistent directory and is outside
this core job rule.

For a saved 0.1.28 job with no custodyRoot or process manifest, cleanup may use only
the exact disposable checkout proved by the saved issue, role, spec cwd and this
machine's core worktrees directory. Pass the saved outer core job start as the legacy
custody boundary only when it is a finite epoch-millisecond value; it predates every
part spawn. Otherwise omit the boundary, and keep unreadable processes uncertain.
Read the issue from the enclosing core job and the role from its authoritative slot:
`job.agent` uses the saved `job.role`; review, suite, vector and Runtime parts use
their named slots. Older agent-job part records do not contain duplicate issue or
role fields. If the enclosing issue or slot role is missing or inconsistent with the
part ID, do not infer it from cwd or scan another checkout.
Require the exit record, a complete process table
that proves the old wrapper is gone, and complete cwd and old process-group scans.
Keep any found process by identity and retry; never signal it from this legacy scan.
A clear bounded scan permits cleanup, but record that historical descendant custody
was unavailable in the job record, history and warning. It cannot prove that an
unobserved helper did not escape both scans.
Do not use a source root, shared folder or an arbitrary spec cwd as a fallback.

Every job starts with `ports.machine.priority(role)` of the machine guard as its
`priority` (nice 19; macOS utility QoS; on Linux a CPU list of Autopilot's share for
agent roles) and that share of the cores as `PDD_CHECK_CPUS` in its environment; with no
`ports.machine` the job runner's defaults apply (nice 19, macOS utility QoS). The
build, repair and conflict rules say: "When you run tests or builds, pass
`$PDD_CHECK_CPUS` as the worker count".

**Cleanup (#3231).** Once per tick, after the jobs advance and before intake,
`sweepFiles` removes each `worktrees/` entry whose issue (`N` or `N-…`) has no job
file (with the intake removal: unlock, `remove -f -f`, the folder, `prune`), and each
`logs/` file of no job with a file (by its `N-` prefix) that is older than 14 days,
then such files oldest first while the folder holds more than 500 MiB. Each step only
warns. The numbers are the guard's `logDays` and `logBytes`.

Jobs run through the [headless job runner](agent-job.prompt.md) with
`agentCommand(state.agent)` and `jobEnvironment(env)`, in `logs/`, with id
`N-ROLE-STAMP`. The prompt names the job's result file path. Every job runs the pdd
that runs the tick: the tick writes `bin/pdd` in `ROOT` (`#!/bin/sh` and `exec 'NODE'
'PACKAGE/bin/pdd.mjs' "$@"`, with this Node and this package, quoted for the shell;
rewritten only when it differs) and puts `ROOT/bin` first on the job's `PATH`, before
any other pdd (for example an older global install). Because a login shell can put
another pdd first again (#3177), every job also gets `PDD_CLI` = `ROOT/bin/pdd`, and
`PDD_SKILLS` = the `skills` folder of this same package (the installed skills can be
older than the engine). The build, repair, conflict and review jobs get `pddCheck
{version, cli, skills}`: the engine's version (`ports.version` or the package version),
`ROOT/bin/pdd`, and `skills {dir, version, read}` (`dir` = `PDD_SKILLS`, `version` = its
`pdd-feature/SKILL.md` `pdd-skills:` value, `read` = the folder that the job's agent
loads by default: Codex and agy `~/.agents/skills`, Claude `$CLAUDE_CONFIG_DIR/skills` when that
is absolute, else `~/.claude/skills`). The [job runner](agent-job.prompt.md) notes when
the agent's shell finds another pdd or the installed skills have another version, and
status shows those notes beside the running process. They file nothing and never end a
job. The briefs use it (#3177): build and repair rule 6 says "Run pdd as "$PDD_CLI" (for
example "$PDD_CLI" test STORY), never as a bare pdd: your shell can find an older pdd
first on PATH. $PDD_CLI is the pdd of this Autopilot."; the approval command of rule 9
is `printf '%s' WORDS | "$PDD_CLI" approve PROMPT --said -`; the conflict and review
briefs say "When you run pdd, run it as "$PDD_CLI", never as a bare pdd."; and the red
texts that name a pdd command name `"$PDD_CLI" test` and `"$PDD_CLI" approve`. Build and
repair rule 1 says "Read these PDD skills and their step files from "$PDD_SKILLS" (for
example "$PDD_SKILLS/pdd-feature/SKILL.md"), never from ~/.agents/skills or
~/.claude/skills: the installed copies can be older than this Autopilot."; the review
and conflict briefs say "Read any PDD skill or rules file from "$PDD_SKILLS"." Every
agent brief names the short job rules file of the package (#3227 fix 5) as
`"$PDD_SKILLS/pdd-prompting/autopilot-job-rules.md"`: build, repair and conflict say
"Read FILE in full before you write the PR body"; review says "Read FILE in full before
you check the PR body".

**No input is cut silently (B2, final battle plan).** Each cap ends with a marker that
says how much is left out and where to read it: the issue text (20,000 characters)
`[cut: N more characters; read the issue for the rest: URL]`, each answer (4,000
characters) the same with the comment URL, the owner table (400 owned files) `[cut: N
more owned files; run pdd owner FILE before you call a file unowned]` (and the table
then never says that every other file is unowned), and the conflict hunks (12,000
characters, 4,000 for an add/add file) `[cut: N more characters; read the conflict in
the files: FILES]`. Each cut is saved in the job (`cuts`) and listed under Not covered in
the evidence record.

- **Build** (in `worktrees/N`): the issue title, URL and body as data from a trusted
  author, and these rules: choose pdd-small-change, pdd-bug or pdd-feature, but make
  ONE PR with prompt, Story, tests and code; this is not a `pdd workflow run`, so no
  `pdd workflow` command, no Herdr, no person wait and no `steps/autopilot.md`. Rule 1
  also carries the choice rule (T10; Serhan, Nov 11: a bug fix is not a big decision;
  big decisions are like adding Autopilot to pdd and how it should work). **Autopilot
  decides** when at least one reasonable fix solves the problem and breaks nothing that
  people use today: the job picks that fix and lists it in the PR body under `Choices
  Autopilot made:`, one line each with its reason (`- CHOICE (REASON)`), with `(changes
  public behavior: WHAT)` when users see a change. For example, "make remove safer" is
  decided (ask y/N only in an interactive terminal, `--yes` skips it, scripts
  unchanged), and nothing is asked. A pdd-bug or pdd-small-change run never asks a
  choice question: it picks the fix that makes the reported behavior right with the
  least surprise (for example a bug in "1 KiB" for 1.9 KiB is decided and listed with
  `(changes public behavior: …)`). Routine compatible choices of command syntax,
  options or data representation are agent decisions when a safe, low-surprise choice
  exists. Preserve existing APIs, defaults and behavior unless the request authorizes a
  change. Several valid designs alone are not a reason to ask. A choice may be a
  question (`needs-person` with `kind` `choice`) only when every reasonable fix breaks
  something that people use today, or, in a pdd-feature run, when the choice actually
  changes product direction. Product direction
  includes whether a new feature area or capability should exist, removing a feature,
  an on-purpose change to a core contract, security, privacy or data policy, or
  something that costs money. An open trusted issue that asks the same product question
  (for example an open decision issue) counts too. Every other choice in a feature is
  decided and listed (small ones: internal names, code structure, tests, message and
  docs wording, small defaults). **A bug fix may
  change an approved rule** (Serhan, D1, Nov 11: "it can change the rule without you
  needed if its a bug"): a pdd-bug or pdd-small-change run whose fix is a change of a
  rule in an approved prompt makes it without asking and lists it under `Choices
  Autopilot made:` with `(changes approved rule: OLD -> NEW)`, so a person sees it; the
  repository's approval setting still applies to the changed prompt (strict approvals
  wait for a person's approval, as before), but the choice rule never asks for it.
  **Two cases always go to a person**, in every run kind and mode (audit, Nov 11): a
  change against a person's recorded answer to an earlier question (an answer in the
  brief, a decision issue), and a change of what blocks merges (a new required check, a
  gate, a hash pin, CI policy). The job does not make such a change by itself: it writes
  the `needs-person` result with `kind` `blocker`. A real blocker (missing access or a secret, an issue that contradicts
  itself, work that cannot be done) is `kind` `blocker` too. A question is ONE plain
  question, 2 or 3 options and the letter that the job recommends, so a person can
  answer with one letter. With `decisions` `decide` (the default) the job never asks a
  choice question and lists every choice; the engine decides a choice question itself
  (Needs a person, below), so only a blocker reaches a person. A vague issue is never a
  reason to ask; a clear issue, or a person's answer in the brief, is built. The brief lists the open issues that the issue names by number and the titles
  of up to 20 other open issues (not PRs, not this issue, only by trusted authors:
  `ports.trusted(row)`, read once per login and tick and shared with the ready rule; a
  failed read is not trusted and warns once per login and tick), so the
  job can see an open decision;
  **the path from file ownership** (debate A, the exact text of A-VERDICT section 6.1):
  the brief has the owner table of the job worktree (`ownerTable`, below; up to 400
  owned files), and the rules say: a file is owned when pdd-bindings.json, a
  `Generated from` header line or a prompt's opening sentence names it (`pdd owner
  FILE` gives the same answer; not sure = owned);
  path a (owned code, the contract changes: the owning prompt first, in the issue's
  words, then Story, tests, code), b (owned code, the contract stays: prompt unchanged;
  quote the restored line or "no contract change"), c (a new code file with new
  behavior: its prompt first, with a binding or header; moved code keeps its owner), d
  (any other file: direct, never a new prompt; a value that a prompt states must agree
  with it; docs take facts from the owning prompt), e (existing unowned code, never a
  file that the PR adds: direct, with a regression test, and the file in the result's
  `adopt` list); never add a
  binding or header for a file of the base unless the issue asks to adopt PDD; tests
  only for a change of the public surface (a test that fails on base), else the done
  check; one `Path: <a|b|c|d|e> — <files> — <owner or unowned> — <prompt changed | quote
  file:line | no contract change | new prompt> — Test: <file | done check>` line per
  path in the PR body; prompt and code may share a commit; never rewrite history;
  focused tests, with the full test command named; the Runtime rule (#3227 fix 5, the
  words of RUNBOOK §15 "Autopilot core jobs"): changed means against the base
  (`git diff --name-only origin/BASE...HEAD`, never since the previous PR head; a Story
  or prompt that a base merge brought in is not changed); commit every change, then run
  `pdd test` for each changed Story and write one `Runtime:` line for each changed Story,
  the verdict first and the Story in the parentheses: `Runtime: PASS (STORY, N/N
  checks)`, `Runtime: FAIL (STORY, N of M checks failed: STEPS)` or `Runtime: not run
  (STORY: REASON)` (STORY the Story file path as `git diff` shows it); a single line with
  no Story is valid only when the PR changes one Story or none; two lines for the same
  Story are red; a PASS of a Story that the PR does not change never counts; a FAIL line
  blocks the merge, and a failed check is a FAIL also when its batch has no verdict.
  `not run` is only for a cause that this PR cannot fix: a native-only prompt, a Story
  with no Runtime test, no verdict with no failed step, or a refusal that pdd gives no
  fix for; a refusal with a fix from pdd (for example a whole number outside the
  interpreter's range: apply the Number spelling that pdd prints) is this PR's work. The
  job does not wait for maintenance: pdd has sent nothing yet, so the job stops pdd and
  writes `Runtime: not run (STORY: maintenance until HH:MM UTC)` with the end time that
  pdd printed (the engine sends that check itself when maintenance ends: merge check
  step 5a); it never sends
  a check again itself and never cuts short a check that pdd has sent. When Runtime could
  not check, the job does not stop and does not invent an interface: it covers the case
  with native tests, ships the PR with the not-run line and puts the reason and the tool
  error in the result's `runtime` with kind `runtime`. One `Evidence:` line
  in the PR body and the same text as the result's `evidence` (below). No review
  verdict or review claim (for example "Review: no must-fix") in the PR body or a
  comment: only the core's fresh reviewer gives one. **Approval (auto and observe
  mode):** observe mode does everything that auto mode does except the merge, so the
  operator's start is the approval of the job's prompt changes in both. For each changed
  `*.prompt.md` that has a Runtime interface block, after its checks pass, the job runs
  `printf '%s' 'WORDS' | pdd approve PROMPT --said -` (trial B5: a prompt with no
  interface block needs no approval, as the prompt gate says; the rule says "A prompt
  with no Runtime interface block needs no approval: do not run pdd approve for it, and
  do not invent an interface.") with WORDS exactly `Operator action: pdd autopilot start --engine
  core in MODE mode for REPO on MACHINE-ID at TIME` (MODE is the real mode, `auto` or
  `observe`, because the words must be true; the machine id, never the host; TIME =
  `state.startedAt`, else `state.activatedAt`) and commits the result in the PR. The
  merge check makes an unapproved changed prompt red in both modes, with the same
  command, so a repair records it. In a repository whose worktree `pdd.json` has
  `strict_approvals: true` the rule says instead: do not run `pdd approve` and do not
  edit an interface status; in auto mode "Autopilot asks a person"; in observe mode
  "Autopilot lists the prompts for a person in its note": observe asks no one (a
  question only makes sense when a merge would follow), adds no `pdd:needs-decision`,
  and its would-merge note lists `Prompts that need a person's approval before a merge
  (strict_approvals): …`. Push the job
  branch and open one PR against BASE with `Fixes #N`; never merge, push to BASE,
  force-push or close the issue, and never assign it or change its labels. The result
  file is JSON: `outcome` `pr` with `pr`, `head`, `promptChanged` (Boolean),
  `evidence` and optional `runtime {state, cause, kind, component, code, detail}`, or
  `outcome` `failed` with `kind` (`pdd` or `job`), `component`, `code`, `cause`
  and a short `detail` without repository code, or `outcome` `needs-person` with one
  clear `question`, only when the job cannot go on without a person's decision. A Runtime check that could not run is
  never a failure.
- **Evidence** (for metrics): one fixed line, `Evidence: runtime=<pass|fail|not-run>
  (<n>/<m>); vectors=<pass|fail|not-run> (<n>/<m>); formal=<proved|bounded|failed|not-run|not-applicable>;
  tests=<pass|fail> (<n>/<m>)` (runtime = `pdd test` on the changed Stories, vectors =
  the replay tests that the change touches: each changed `*.vectors.test.*` file and each
  vector test file that names a changed scenario file, run with `node --test` (the merge
  check runs the same files and compares the counts), formal = the changed formal
  tests, tests = the focused tests; a count may be left out). The job prompt says this. The tick parses it with an allowlist: the first PR body line
  that starts with `Evidence:` after the Runtime-line marks go, else the result's
  `evidence`; each `key=value` part with a known key and value is kept once, with its
  count when it is `n/m` with n ≤ m (never for formal); anything else is dropped. The
  parsed value is saved on the job (`evidence`, or null) and in its history line. The
  merge check parses it from the PR body each time and makes it a red finding when it
  contradicts itself or the checks: a `fail` (or `formal=failed`), a `pass` with fewer
  passed than total or 0 of 0, or a runtime value other than `fail` that disagrees
  with the PR's Runtime line (PASS or not run).
- **Repair** (same worktree and branch): the red findings, the job log folder, then
  the build rules; push to the same branch, no new PR, and update the `Runtime:` and
  `Evidence:` lines when they change, with "changed" against `origin/BASE...HEAD`. After
  a merge from the base, the repair and the conflict update check that the fix is still
  needed (#3227 fix 5): the PR's changed tests run on the new merge base in a throwaway
  worktree; when they pass there too, the base holds the fix, and the PR keeps only what
  the base does not hold and says so in its body. **Reproduce before a repair round
  (#3247):** when the red findings include a failed CI check or a failed full test suite,
  the engine extracts and puts structured failure reproduction details in the repair brief
  for each failed check: the failing test names (with files when known, from
  `failingTests` and check-run test annotations), the redacted failing lines of the log
  (`failingLogLines(text, limit=25)`, exported: strips GitHub Actions step prefixes with
  optional UTF-8 BOM and ANSI escape sequences before secret redaction and failure parsing;
  extracts TAP failure blocks, spec `✖ failing tests:` detail blocks without letting earlier
  spec tree rows or passing siblings starve them, assertion/error lines, check-run output
  and annotations of failed check runs, and `gh run view RUN --repo REPO --log-failed` once
  per failed workflow run when a run id is known, falling back to the last non-empty lines),
  and the environment of the failure (CI check name vs local
  full-suite runner, platform, worker concurrency `$PDD_CHECK_CPUS` vs CI runner
  concurrency, `CI=true`, and clean-checkout or permission context such as `/proc` or
  `EACCES`). The brief requires the repair agent to first run those exact failing tests in
  the matching environment and observe them fail before changing code, to check
  `origin/BASE` (`git merge-base origin/BASE HEAD` in a throwaway worktree, #3181) when an
  untouched test fails and report `{"outcome": "failed", "kind": "pdd", "component":
  "base-suite", "code": "base-test-red", "cause", "detail"}` without guessing an edit when
  the test fails on `origin/BASE` too, and after a fix to run the same tests in the same
  environment and confirm they pass before pushing. When every red finding of the round is
  a CI or full-suite failure and no reproduction rerun has run at this head yet, the brief
  also allows `{"outcome": "not reproduced", "command", "detail"?}` (`"not-reproduced"`
  accepted too) when the failure does not reproduce and the repair made no code changes.
- **Review** (in `worktrees/N-review`, a detached checkout of the head): a fresh agent
  that did not write the change. It gets the path checks' table of the PR's changed
  files, each in one of three states (owned on the base, with its owner; unowned on the
  base; new in this PR, not on the base; or not checked when main's owners cannot be
  read), and the R5 hints (below), and checks the
  issue fit; (2) Path and (3) Tests with the exact text of A-VERDICT section 6.2 (the
  Path lines match the owner table, disputed only by naming a missed binding, header or
  prompt line; a and c trace to the issue; b keeps the contract; d agrees with any
  prompt that states a changed value; a new code file with new behavior takes path c
  with a binding or header, which the reviewer never asks to remove; must-fixes: a
  new prompt for a non-code file, owned code that disagrees with its prompt; the
  reviewer does not report what the path checks (below) already check (R1, R3, R4, R6
  and R7); a config or metadata file (package.json, a lock file, CI settings) needs no
  prompt and no Story, so never a new prompt for it, and a test only when the change
  alters a result that users see (#3227 fix 5, rule 8); never a new
  prompt for an unowned file; never commit order; a missing test is a must-fix only
  with the surface and the result named; no test that only copies a value from the
  diff); an honest Runtime line and no unrelated or unsafe change; and (6) **the choices
  (T10)**: every choice that the issue did not settle is listed under `Choices Autopilot
  made:` with its reason (with `(changes public behavior: …)` when users see a change,
  and `(changes approved rule: OLD -> NEW)` when a bug or small-change fix changes a rule
  of an approved prompt; a missing such mark is a P2 must-fix: fix the list); a missing
  or wrong line is a P2 must-fix (fix the list), never a decision item. A change against
  a person's recorded answer to an earlier question, or a change of what blocks merges,
  is a P1 must-fix in every mode: undo it, or end with the `needs-person` result `kind`
  `blocker` (so such a PR never merges by itself). A feature that changes an approved
  rule on its own, with no product-direction answer, is a decision item with `ask`. In a pdd-bug or pdd-small-change PR a
  decision item is never a question: only a repair or a "list it" fix. With `decisions`
  `ask`, only a product-direction choice of a feature PR (rule 1) that the job made
  instead of asking is a P2 must-fix with the word `decision:` after its severity or its
  place (`P2 decision: …` or `P2 FILE:LINE decision: …`), and the result's `question`,
  `options` (2 or 3) and `recommended` (a letter) are the one question for a person.
  With `decisions` `decide`, the brief has no decision item. A person's answer to an earlier question is in the brief (the same answer text as the build), so a
  settled choice is not asked again. The brief has the linked open issues: each open
  issue (not a PR, not this issue, only by trusted authors, from the tick's issue list)
  that the issue title, the issue body or the PR body names by number (`#N`, `REPO#N` or
  its URL), or whose title or body names a file that the PR changes by its full path, at
  most 5, each body cut to 2,000 characters; or "(none)". A Runtime FAIL line in the PR body means a FAIL verdict. **It reads the diff in parts** (battle plans, Nov 11: a tool output over about 10,000 tokens loses its middle; 70 of 146 review diff reads were cut): first `git diff --stat origin/BASE...HEAD`, then one changed file per command (`git diff origin/BASE...HEAD -- FILE`), and a file whose diff is larger than about 30 KB in hunks (for example with `git diff -U3 origin/BASE...HEAD -- FILE | sed -n 'A,Bp'`); never the whole PR's diff in one call. The brief says the limit in these words: "A tool output over about 10,000 tokens loses its middle." The verdict's summary ends with one line `Read: FILE, FILE, …` that names every changed file that it read in full (the engine check that blocks a PASS without it comes in 0.1.30). It writes no files and makes no GitHub write. Its
  result is `{verdict: PASS|FAIL, head, summary, mustFix[], question?, options?,
  recommended?}`. **A decision is a question, not a repair (only with `decisions`
  `ask`):** when a blocking item of a FAIL is a decision item (P1 or P2, then the word
  `decision:` within its first 200 characters), the merge check ends the job as **needs
  a person** (below), in auto and in observe mode (a question is not a merge; observe
  mode only leaves out the merge), with that one question (the
  reviewer's `question`, else "The review found a choice that issue #N did not make: ITEM.
  Which option do you want?"), not a repair round, also when other items exist (the
  answer can change the whole change; the next build reads the answer and the review
  runs again). The open PR gets one note (`<!-- pdd:autopilot-core:needs-decision-pr:P -->`):
  it waits for the answer and does not merge; the next build closes it as usual. With
  `decisions` `decide`, a decision item is an ordinary must-fix (a repair), never a
  question. Each must-fix item starts
  with its severity and place: `P1 file:line …` (wrong behavior or unsafe), `P2 file:line …`
  (fix before the merge) or `P3 file:line …` (a follow-up); a PASS lists only P3 items
  (the scoped check is asked the same). **Fail closed:** an item is a follow-up only when
  it starts with P3 and names no P1 or P2 anywhere; every other item blocks, also in a
  PASS (a numbered, a "Severity P2:" or an untagged item, or "P3/P1"). The split comes
  before each list is cut to 20 items, so no blocking item is lost. The verdict is PASS
  only when no item blocks and the reviewer said PASS or listed at least one follow-up. A
  string `mustFix` is one item; a missing or empty list is none, and a FAIL with no item
  stays a FAIL (its red line says "see the review comment on the PR"); a verdict that is
  not exactly PASS or FAIL is no verdict. The tick lists them as follow-ups in the review comment,
  in one section at the end of the PR body (a follow-up never reads as a `Runtime:`, `Path:`
  or `Evidence:` line) and in one note on the issue (marker
  `<!-- pdd:autopilot-core:follow-ups:N -->`), each updated in place and with no item twice.
  A follow-up never closes an issue: an issue reference (`#18`, `owner/repo#18` or an issue
  URL) becomes `issue 18` (`owner/repo issue 18`).
- **Suite** (in `worktrees/N-suite`): `node bin/pdd.mjs workflow suite --command
  TEST --timeout 0` through the [shared full-suite queue](test-suite-queue.prompt.md):
  no fixed time limit (the process rule watches it), with `CI=true` in its environment so
  watch modes end. Exit 0 is green; any other
  exit code of the repository's test command is a red suite, and repairs apply. Only a
  failure of the runner itself is not a test result: a run that died (no exit record)
  or was killed by a signal, the wrapper's exit 127 (could not start), no output at
  all, or a runner line in the log ("Shared test suite queue failed", "Test suite
  execution timeout", "Test suite could not start", "Test suite ended by SIG…",
  "Test suite descendants could not be confirmed", "Supply a suite command"). It
  starts again in the same checkout, at most twice. On the 3rd failure, a runner that
  died on all 3 tries (the deaths count over every try of this suite run) is a
  `no-result` end; any other runner failure ends the job with a
  `pdd` cause `suite-broken`. It never uses a repair. A fresh checkout has no
  installed dependencies: when it has `package-lock.json` and `package.json` lists
  dependencies (`dependencies`, `devDependencies` or `optionalDependencies`), the suite
  job is `/bin/sh -c 'npm ci --ignore-scripts --no-audit --no-fund || …exit 86; exec
  "$@"'` before the same suite command. An install failure (exit 86 or the line
  "Autopilot core: dependency install failed") is a runner failure, not a red suite.
  A repository with no dependencies installs nothing.

A running build, repair or conflict agent that T1 stops ends as `no-result` with no
valid result file (the no-result rules apply, with the owner of
[Stop owners](#stop-owners): `service` for an AI-service problem, `issue` for a repeated
hang, else `machine`); with one it goes on as an exited job. An agent that exits with no
result after a repeated hang is an `issue` stop too. A
reviewer that T1 stops counts as no verdict unless its result file is valid. An exited or dead job: a valid `pr` result moves
to the merge check in the same tick. The PR number may be a number or a string of
digits (an optional `#`); it becomes an integer above 0. The head is 40 hex digits in
any case and is saved in lower case. Any other PR value is no result. A repair result
`{"outcome": "not reproduced", "command", "detail"?}` (`"not-reproduced"` accepted too)
with a nonblank `command` counts as a job result (`produced`). When the round had only CI
or full-suite red findings (including no prior `Review: FAIL` at this head) and no
reproduction rerun has run at this head yet, the engine reads the PR on GitHub (finishing
a merge, or ending as `pr-closed` or `head-moved`, when the PR changed while the repair
ran), resets any uncommitted edits in the job worktree to the PR head, refunds the
tentative `repairs` and `rounds` entries of that round, and reruns the failing check once:
when `ci` was red, failed CI is rerun via 2xx `POST
repos/REPO/actions/runs/ID/rerun-failed-jobs` (falling back to `/rerun` or `POST
repos/REPO/check-runs/ID/rerequest`), ending as `checks-red` without recording a rerun if
no failed CI check could be rerun, and treating an unchanged pre-rerun failed-check
signature as pending for up to 2 minutes until GitHub updates those failed checks; passing
checks (`review`, `suite`, `vectors`, `coverage`, `untested`) at this head for the non-red
checks are restored (`suite` cleared when `suite` was red), `reproduceRerun {head, at,
command, detail, kinds}` is recorded, and the job moves back to phase `pr` in the same
tick. A second `"not reproduced"` at the same head, or one when non-CI/non-suite checks
were red, ends the job as `checks-red`. A `failed` result ends
with the agent's cause (when a repair reports `kind: "pdd"` and `code: "base-test-red"`
for #3181, its tentative `repairs` increment is refunded first); anything else ends with
`no-result`.

**Needs a person.** A result `{"outcome": "needs-person", "kind", "question", "options"?,
"recommended"?}` with a nonblank question counts as a job result (`produced`). `kind` is
`blocker` (missing access or a secret, an issue that contradicts itself, work that
cannot be done, or one of the two cases of rule 1 that always go to a person) or
`choice`; no `kind` counts as `choice`. **A choice that Autopilot decides is never
posted** (T10): with `decisions` `decide`, and with `ask` after a person already
answered a question on this issue (at most one choice question per issue), the engine
starts the same agent role once more in the same worktree (a build gets its build
brief, a repair the same reds; `decided {question, role, at}` is saved and ends up in
the history line) with the question and "Autopilot decides this choice: do not ask.
Pick the recommended option, or the fix that makes the reported behavior right with
the least surprise and breaks nothing that people use today; build it, and list it
first under Choices Autopilot made:, marked (big), with (changes public behavior: …)
when users see a change." A second decided choice in the same job, or one from another
role, ends the job (`job` cause `no-decision`). Every other `needs-person` result (a
blocker, or a choice with `ask` that follows rule 1) goes
through the resumable END steps with a question instead of a cause; its END history line
has `ask: KIND`. Read the claim again
before each write (hand over when another machine owns it); post one issue comment
`Autopilot needs a decision from a person to go on with this issue:`, the question as
`> ` quote lines, and "Please answer in a comment (one letter is enough). Autopilot
reads your answer at its next check, removes the `pdd:needs-decision` label itself and
goes on.", with the marker
`<!-- pdd:autopilot-core:question:N:JOB-ID -->` (found again after an uncertain post). The question text
(T10 format) is the plain question on one line, then, with 2 or 3 nonblank options,
one line per option `A) OPTION`, `B) …`, `C) …`, the recommended one ending with
` (recommended)` (`recommended` is a letter, a 1-based number or the option text; a
leading `A:`, `A)` or `A.` that the agent wrote into an option is dropped, so the letter
shows once), and
the line `Reply with one letter, for example: X` (X the recommended letter, else A);
with fewer than 2 or more than 3 options the question goes alone. The same format is
used for a review decision. Then add `pdd:needs-decision` (never `pdd:stuck`); delete this machine's claim comment and
remove `pdd:working`; clean up locally with outcome `needs-person`. The slot is free.
**A trusted reply is the signal** (trial, Nov 11): the ready rule skips an issue with
`pdd:needs-decision`, but when such an issue's `updated_at` differs from the one saved
for it in the machine state (`decisionSeen`, so each change is read once), the core
reads the answer below; with a trusted reply after the question (one that starts with
an option letter, or any other), it removes `pdd:needs-decision` itself and the issue is
ready in the same tick. A strict repository's prompt approval question (its text names
`(strict_approvals)`) is not ended by a reply: it waits for the approval and the label
removal. A trusted person's removal of the label still works. When the core claims an issue with comments, it reads
the latest question comment that this engine posted (author = the engine's own login,
`GET user`, and a marker that names this issue; a marker comment by anyone else is
not a question) and the comments after it by trusted people (`ports.trusted`), leaving
out comments with a `<!-- pdd:` marker and claim comments. A trusted reply, or a
removal of `pdd:needs-decision` after the question by a trusted person (the timeline
`unlabeled` event's actor), answers it; otherwise the core puts the label back, undoes
its claim (claim comment and `pdd:working`) and starts nothing. The next build prompt
then has the question and those answers as data, or "no written answer" when there
is none.

**Owner table** (`ownerRead(fs, root, files)` and `ownerTable(fs, root, files)`, both
exported; the one owner function of the engine) reads a checkout with `findOwners` of
the [file owner lookup](file-owner.prompt.md), the same reader as `pdd owner`; the
engine has no second reader. Its `files` port is the checkout's Git files; its `read`
port reads through `ctx.fs` and gives no content for a missing path or a path that is
not a regular file (a submodule folder). `ownerRead` returns `{owners, unchecked,
bindings}`, and `ownerTable` is its `owners`. `owners` maps each file with an owner to
`{prompt, how, owners, certain, note}`: `prompt` is the lookup's `owner` and `how` its
`source` (`binding`, `header` or `prose`). A file with no owner whose answer is not
certain is never owned by an unknown prompt: `unchecked` maps it to its cause,
`pdd-bindings.json unreadable` when the lookup's note says that pdd-bindings.json could
not be read, else `the file could not be read`. `bindings` is false only when the
reader cannot use the checkout's `pdd-bindings.json`: the reader's `resolveOwners`
gives a path that nothing names an uncertain answer with that text (its first 64 KiB,
read with the same port, as `findOwners` reads it; a missing file is readable). In text
an owner is `PROMPT (binding)`, `PROMPT (header)`, `PROMPT (prose, not certain: treat as
owned)`, or another uncertain answer `PROMPT (HOW, not certain: NOTE)`. The build brief
lists the owned files; with `bindings` false it adds the line `- (pdd-bindings.json
cannot be read here, so no binding is known)`. **Path e** results carry `adopt` (file
paths): the job keeps the union of the `adopt` lists of its results (`job.adopt`). It
files them only when the PR passed every check at its final head, right before the
merge note or the would-merge note, once per job: one deduped PDD report
(`autopilot-core` / `adopt-pdd`) with only the paths that the path checks of that head
call unowned on the base (so a new file never). It never blocks the job.

## Merge check

Phase `pr` has no deadline. Each tick, in order (during a step wait, nothing below
runs until its end):

1. Read the PR. Merged: finish as merged, also when quiet, so END never runs on a
   merged issue. Quiet (nothing ran and nothing changed for the quiet period), or a PR
   read that fails while quiet: a **step stop**, never an END ("the PR checks made no
   progress for N minutes (nothing ran and nothing changed); last error: …"). Its owner
   and code come from the last saved error and its step (`lastErrorStep`): a service
   error is `service`; else `pdd` with `base-check` (the base check could not verify),
   `claim-error` (a claim that is not confirmed), `merge-check-tool` (a failed PR read,
   a GitHub or Git error, a refused `gh pr merge`), `bindings-unreadable` (the merge
   waited for an unreadable base `pdd-bindings.json`, step 5; main's file, not the
   issue), `owner-unreadable` (it waited for another base file that the path checks
   could not read) or `step-quiet` (no error). It becomes a step wait ([Stop
   owners](#stop-owners)). Closed: end
   `pr-closed`. The PR head SHA, head branch or base differs from the job: end
   `head-moved`.
2. `Runtime: not run (…)` is allowed, and the PR body is not rewritten. When the
   job's `runtime` has state `not-run` and kind `runtime` (Runtime could not check),
   file or count one report through the [report owner](autopilot-reports.prompt.md)
   (with `runtimeRepo` and `runtimeOwner`) with the cause `{kind: runtime, component, code, text, detail, shipped: true}`
   (component default `pdd-test`, code default `not-run`), once per job and
   component/code (`job.runtimeReport`), and only when the Runtime resend (5a) has no
   check left to send for this head: while it may still send one, no report is filed.
   It never blocks or ends the job. A not-run
   with no Runtime kind (for example no prompt changed) files nothing.
3. Red findings. The Runtime gate is an allowlist (fail closed). A Runtime line is a
   PR body line that, after heading, list, quote, table, bold and code marks go,
   starts with "Runtime" or holds "Runtime:". Its value, after leading signs such as
   an emoji, names its Story in the parentheses after the verdict (`Runtime: PASS (STORY,
   …)`, the form of the briefs and the RUNBOOK); a Story path first (`Runtime: STORY
   PASS (…)`) is read too. Then the verdict must start with PASS (or PASSED) or "not run", in any
   case; any other value is red, and the repair prompt quotes the line. **Per-Story
   lines (#3227):** with more than one Runtime line, each line names its Story and no
   Story has two lines (else red); different Stories may have different verdicts. A
   single line with no Story is accepted only when the change has at most one changed
   Story (else red: one line per changed Story). With Story lines, each changed Story
   needs its own line, and a PASS line of a Story that the PR does not change is red,
   unless that Story's own tests reach a changed prompt (their upload, `footprint` of
   the Story's tests, holds it): such a Story is a changed Story too (rule 6: "or whose
   test reaches a changed prompt"), so its PASS line needs the cover below like any
   changed Story (Claude round 5, MF-G1). **The consumer closure (B1, final battle
   plan):** with a changed prompt, the engine lists every Story whose test reaches it,
   with no AI call: `reach(prompts)` of the reader port (`captureSource` of each test of
   the head at the clean checkout, one at a time, the transitive call targets included;
   a test port gives its `footprints` map), read once per head and prompt set (saved as
   `reach`). A changed Story (Story file, test file or consumer) needs a passing current
   check or its own Runtime line; a consumer with neither is red: "S reaches the changed
   prompt P (its tests upload it), but it has no passing pdd test check at this source
   and no Runtime line. Run "$PDD_CLI" test for S at this head, or write "Runtime: not
   run (S: REASON)"."; a consumer with a "not run" line, or with no pass, is checked
   against its saved rows like any changed Story (fix 1: a failed row is red). There is
   no cap (Serhan, D3: "it should check all"): every consumer counts, however many; rule
   6 asks to send them in one `pdd test` batch where it can. Only a consumer that Runtime
   could not check (its deciding rows have no verdict, no failed check and no refusal:
   maintenance, a service failure) is no red; then the merge note and the record say
   `Runtime: not run (N Stories reach PROMPT; checked K)` (K the consumers with a passing
   current check), never a silent pass and never a way to skip work. The single-line
   rule (one line with no Story) counts only Story and test file changes. On pdd, a
   change to `prompts/cli/runtime-client.prompt.md` reads its consumers in one tick in
   under 60 s (a test checks it). The result's `runtime.state` (lower case, spaces as `-`) must be
   absent, `pass` or `not-run`, and must agree with the body when all lines have one
   verdict; else red. With per-Story lines, if any Story says `not run`, the result
   state cannot be `pass`; it must be absent or `not-run`. A not-run Story remains
   unverified; a pass for another Story does not mark it passed. A body with no
   Runtime line is red when the change has a `*.prompt.md` (Git decides, also when the
   result says `"promptChanged": false`); with no changed prompt it is red unless the
   result says `"promptChanged": false`. **A Runtime pass must be true (T01):** every
   positive Runtime claim is checked: a "Runtime: PASS" line, an Evidence part
   `runtime=pass` (of the PR body, else of the result) and a result `runtime.state`
   `pass`. With no positive claim (every line says "not run" and nothing else claims a
   pass), no cover is needed: only the line form above and the saved-row checks of
   every line below apply (Claude round 5, MF-G2). With Story lines, only the Stories of PASS lines need the cover below, and a
   changed prompt that no passing check reaches is fine when it is in the upload of the
   tests of a Story with a not-run line (that line says the prompt was not checked). A
   claim counts only when the saved Runtime checks cover the change at the
   agent's exact head (`agentHead`, the head of the last build, repair or conflict
   result). The read is saved as `coverage` for that head; a new agent result and a
   repair clear it (and `vectors`), because `pdd test` saves its checks outside the
   repository, so a repair that only runs `pdd test` keeps the same head. The changed
   files are `git diff --name-only -z --diff-filter=d origin/BASE...HEAD` (NUL mode, so
   every name stays exact). The read uses a clean checkout of that head
   (`worktrees/N-agent`): the Stories and their tests come from `findTests` there, with
   fixture projects excluded (as a full `pdd test` does), and `savedStoryEvidence` of the
   [runtime client](runtime-client.prompt.md) reads the checks that `pdd test` saved for
   the job worktree (`root`) and compares their source with the clean checkout
   (`comparisonRoot`, with `withTests`, so each row names the tests that its check ran).
   So an uncommitted or untracked file of the job worktree never counts as the head. A
   Story is changed when its Story file or one of its test files changed. Each test of a
   Story is its own scope: for each test, the latest check of exactly this source that
   ran it (`current`, the largest `at`) decides; a tie with a check that did not pass, or
   a newer failed or no-verdict check, is not a pass. So independent checks of different
   tests of one Story combine (two big tests that cannot go in one upload are checked
   apart), and no check lends its pass to a test that it did not run. A Story passes when
   every scope that a current check has passes. Each changed Story needs such a pass, and
   each changed test must have a passing deciding check of its own; a changed Story file is
   in the upload of every test of that Story, so each test of a changed Story needs its
   own passing deciding check too (Claude round 4). Each changed
   `*.prompt.md` must be in the upload of a passing deciding check: `captureSource` of
   exactly that check's tests at the clean checkout (its `files`, what the check sent),
   never the footprint of other, unchecked tests of the Story; each Story in its own error boundary (changed Stories
   first; stop when every changed prompt is reached), so a broken unrelated Story never
   hides a healthy one, and unchecked siblings never make the selection too big. Else red: "CLAIM, but
   the saved pdd test checks at head H do not cover FILES (the saved check of S is for
   another source: a stale Runtime batch, for example an older commit or files that are
   not committed; the latest check of S at this source did not pass; no check of S at this
   source ran T; the source of S
   could not be read: CAUSE). A PASS of other Stories does not count. Run pdd test for
   the Stories of these changes at this head, or write "Runtime: not run (REASON)" (and
   runtime=not-run) when they have no Runtime check (for example a native-only
   prompt)." CLAIM names each claim, for example `The PR body says
   "Runtime: PASS"`. A PR that changes no prompt, no Story and no Story test needs no
   coverage. A reader error (for example `findTests` throws, or the clean checkout cannot
   be made) is red with its cause, never a tick error. The reader is a port: `ports.runtimeEvidence({root, tree, head}, ctx)`
   returns `{stories, storyFiles, tests, footprint(story, row)}` (`tests` rows `{path,
   files, stories}`; story rows may have `tests`; `footprint` gives the upload `{files}`
   of the row's tests, or `{error}`); a test port may give a `footprints` map instead
   (then a row with no `tests` covers its Story's tests). Rows that were never sent
   (`sent: false`) never count as a pass and never decide a scope of this cover.
   **Every Runtime line is checked against the saved rows (#3227 fix 1):** the read above
   runs for each PR with a Runtime line, also when every line says "not run" (the line
   form rules above still apply only with a PASS claim or Story lines). Each changed
   Story that the cover above does not check (it has no PASS line, or the one line is
   not a PASS) is checked against its deciding rows at this source: for each of its
   tests, the latest current row that names it, also a row that was never sent.
   (a) A row with failed checks, or with a failed verdict, is red, also when the batch
   has no verdict: "The latest saved pdd test check of S at head H has N failed checks
   (steps: …). A failed check is a FAIL, also when the batch has no verdict: fix the
   cause (the code, the prompt or the test) and run pdd test again at this head."
   (b) A refusal that pdd can fix is red once per Story and refusal code in the job, and
   only while a repair is left: pdd saved a fix text for it (`advice`: a pdd warning that
   names the test and the code, for example `scenario-integer-out-of-range` with the
   exact Number spelling, or the refusal's own `fix`). "The saved pdd test check of S at
   head H was refused before execution (CODE). pdd printed the fix: ADVICE Apply the fix
   that pdd prints and run pdd test again at this head."
   (c) Runtime coverage must not go down. When a changed Story has no deciding row, a
   refused row, or a row that did not pass for another reason than the service, the
   engine reads the saved checks again for a clean checkout of the merge base
   (`git merge-base origin/BASE HEAD`, `worktrees/N-fork`), with `anyRoot` (the
   batches of every folder of this machine; only the source decides) and `limit` 200
   (the newest batches). A Story that passes there by the scope rule above is red:
   "Runtime coverage went down: S had a passing pdd test check at the merge base B, but
   at head H it has REASON. A PR must not lose a Runtime pass: make the check of S pass
   again at this head." A row with no verdict, no failed check and no refusal (an AI
   provider failure, maintenance, a busy or interrupted check) is never red here: the
   engine sends such a check again (B5). A merge base read error is not red: the engine
   warns, and the record keeps the error. The port gets `{root, tree, head, base:
   true}` for the merge base read. **Prompt gate**
   (once per head, saved as `approvals {head, strict, problems}`): after a fetch of the
   base and the branch, each changed prompt of `git diff --name-status --find-renames
   origin/BASE...HEAD` (added, modified, renamed or copied; the new path) is read in a
   clean checkout of the head (`worktrees/N-approve`) with the
   [preflight](runtime-preflight.prompt.md)'s own `readPrompt` and `promptRefusal`. A
   problem is: a refusal (two blocks, invalid JSON, a bad status, a stale prose hash), a
   status other than `approved`, an interface that the base had and the head removed
   (no interface on both sides is not an approval matter), or an approved status with
   no approval: not the same interface and prose hash as the base version at the old
   path (a pure rename keeps the approval that Git has), and no entry for that path and
   prose hash in the approval journal of the repository's common Git dir
   (`readPromptApprovals`). Its finding says: set the status to "draft", then run `pdd
   approve` (it records an approval only for a draft or stale prompt). A strict
   repository accepts only a person's approval: a trusted APPROVED review of the head
   on GitHub, or a journal entry made at a terminal. `strict` is true
   when `strict_approvals` is true in `pdd.json` on the base or at the head. In auto
   mode, problems in a strict repository end the job as **needs a person** (below)
   with the question "PR #P changes prompts that need a person's approval in this
   repository (strict_approvals): … Please approve the PR on GitHub (or approve each
   prompt with pdd approve on its branch and push), then remove pdd:needs-decision:
   Autopilot checks the same PR again, with no new build. To give up on it, close the
   PR.", the PR stays open with one note `<!-- pdd:autopilot-core:needs-approval:P -->`.
   After a trusted removal of the label, intake resumes that PR (phase `pr`, its
   branch in the job worktree, `resumed: true`) instead of a new build (a failed fetch or
   checkout of that branch undoes the claim and removes the worktree, as other intake
   failures do; the next tick tries again); in other repositories they are red,
   with the approval command and words in the finding (one repair, then END as usual).
   Observe mode approves as auto mode does, with "in observe mode" in the words (above),
   so problems outside a strict repository are red there too. In a strict repository
   observe mode asks no person: it lists the problems in its "would merge" note.
   **Path checks** (debate A section 6.3 and #3239; no AI, once per head and PR body,
   saved as `paths`, and read again when its result has unchecked files and the base
   tip moved; the rules are the pure, exported `pathRules({changed, baseFiles, before,
   after, body, adopting})`, where `before` and `after` are `ownerRead` results, and
   it returns `{reds, owners, unowned, unchecked, wait, quotes}`). The changed files
   come from Git, never from the PR body: `git diff
   --name-status --find-renames origin/BASE...HEAD` (from the merge base; a renamed file
   is its new path, with its source). The owner tables before and after come from clean
   checkouts of the base tip and the head. Each changed file has one state: **owned**
   (the base table has the file, or the source of a renamed file), **unowned on the
   base** (the file or its source is a file of the base tip with no owner), **new in
   this PR** (not a file of the base tip) or **not checked** (the base answer for the
   file or its source is unchecked, see the Owner table). The PR body gives only the path letter of
   each file: from each `Path:` line only the files field, the text after the letter up
   to the next dash separator ` — `, ` – ` or ` - ` (T09). The words of that field
   (split at white space, commas, semicolons, quotes, backticks, brackets and `|`, each
   without a leading `./` or a trailing `.` or `:`) name a file only when they are a
   changed file or the source of a renamed one; every other word, for example a
   prompt in parentheses or a file of the test text, is ignored. Red (each text once):
   R1 an owned file on a path d or e line (`F is owned by OWNER, so it cannot take path
   X: use path a or b.`) or on no `Path:` line (`F is owned by OWNER and this PR changes
   it, but no Path line names it in its files field: put it on a path a or b line.`);
   R7 a new file on a path e line (`F is new in this PR (not on the base), so it cannot
   take path e (existing code that no prompt owns): a new code file takes path c, with
   its prompt and a binding or a Generated from header; any other new file takes path
   d.`); R3 an added prompt that no added file of the PR (with an issue that asks to
   "adopt PDD", any changed file) names by a binding or header at the head (the head
   table's `how` is `binding` or `header` and its `owners` has the prompt; the opening
   sentence alone is not enough: `P is a new prompt that owns no new code file of this
   PR by a binding or header (its opening sentence alone is not enough): give the new
   code file a binding or a Generated from header (path c); a non-code change takes
   path d, with no new prompt.`); R4 a file of the base with no owner (for a renamed
   file, its source) that the head gives a binding or header, unless the issue asks to
   adopt PDD; R6 no `Path:` line; R8 the PR changes `pdd-bindings.json`, the base one
   can be read and the head's cannot (`pdd-bindings.json cannot be read at this head: fix it (pdd owner
   needs valid JSON with schema_version pdd.bindings.v1 and a modules array, at most 64
   KiB).`). A not-checked file gets no R1, R7 or R4 red: when the base
   `pdd-bindings.json` cannot be read, that is main's problem, not this PR's. Then
   `unchecked` lists the not-checked files and `wait` says why (`pdd-bindings.json
   cannot be read on main, so the owners of F1, F2 are not checked`, or `F could not be
   read on main`); see the merge wait in step 5. R5 is only a hint for the reviewer:
   prompts at the head that mention a changed file that is unowned on the base. The
   saved `paths` also has the reviewer's table, one line per changed file: `- F: owned
   on the base by OWNER`, `- F: unowned on the base`, `- F: new in this PR (not on the
   base)` or `- F: not checked (pdd-bindings.json unreadable on main)` (or `(the file
   could not be read on main)`), with ` (moved from S)` after a renamed F and `, deleted
   in this PR` after the state of a deleted F. `quotes` maps each R1, R7, R3 and R4 red
   to what the check read for it: `read "FIELD" in the files field of the line "LINE"`
   (R1 on a path d or e line, R7; LINE is `Path: X…`, at most 200 characters), `read
   these files fields: "FIELD"; "FIELD"` (R1 on no Path line, at most 5 fields), `read
   these head owners of the new files: F: OWNER; G: no owner` (R3, at most 5) or `read
   the head owner of F: OWNER` (R4).
   **A changed Story with no Runtime test (#3241
   case 1, once per agent head, saved as `untested`):** each Story whose Story file
   changed against the base and that `findTests` at the clean head checkout lists as
   untested (`untested`, fixture projects excluded) is red, with pdd's "has no test:
   expected …" line: "A missing test is not a reason for "Runtime: not run": write a
   Runtime test for each such Story (in test/runtime/ or tests/runtime/ when the
   repository keeps its own tests in test/ or tests/), one step for each of its criteria,
   and run "$PDD_CLI" test; or, when bound ports cannot fake the effect, mark the owning
   prompt's interface native-only with a reason." It is not red when the PR changes at
   least one prompt and every changed prompt's interface is `native-only` (the Story is
   checked natively). A read error adds no red (the T01 read names it). The reader is a
   port, `ports.untestedStories(tree)` → `{untested, visible}`. Then a
   failed CI check
   (check runs and commit statuses of the head; neutral and skipped pass); else
   a review FAIL or a failed suite. With no red finding yet, start the review and
   the suite for this head when missing; CI may still be pending. A reviewer that
   twice gives no valid verdict for the head ends as `no-result`; no test command
   ends `no-test-command`; a broken suite ends `suite-broken`. The tick posts each verdict once as a PR comment with
   the head, summary and must-fix list.
   **The engine's own replay and formal run (T04):** with the review and the suite, at the
   final head (once per head, saved as `vectors`; a repair clears it, so a repair at the
   same head runs it again, like the suite). Before a new head or schema replaces a
   running saved replay run, snapshot its live process identity and save the job, then
   use the headless job runner's cleanup. Replace it only after that cleanup confirms
   every saved process is gone. If the snapshot or cleanup cannot confirm ownership,
   keep the old `vectors` record and retry it on a later tick. The set is complete: each changed
   `*.vectors.test.*` and `*.formal.test.*` file, and each `*.vectors.test.*` file that
   names any changed scenario file (a changed `.json` under a `test`, `tests`, `runtime`
   or `vectors` folder, by its base name: `git grep -z -l -F` at the head, 100 names per
   call). Discovery is in NUL mode (`-z`), so every name stays exact. Only node:test
   files run: a `.js`, `.mjs` or `.cjs` file whose text at the head holds `node:test`, or
   that imports by a relative path (two levels at most, inside the checkout) a file that
   holds it (pdd's replay helpers), and whose absolute path in the checkout has no
   backslash (Node refuses such a module path). Each other file is "Not run by Autopilot (REASON)" in the note. It
   still counts for its kind: a kind with such a file cannot substantiate a positive
   claim (below), for a mixed set too. More than 400 files, or a command over 100,000 bytes, runs
   nothing: "not run (too many replay and formal files: N; the limit is 400)", never a
   part of the set. The run is one bash command through the machine's suite queue in a
   clean checkout (`worktrees/N-vectors`, the suite's dependency install, `CI=true`),
   watched by the process rule (role `vectors`, like the suite). **Per-file accounting
   (Codex round 4):** each file runs alone, directly as a script with the TAP reporter
   (`node --test-reporter=tap -- 'ABSOLUTE-FILE' 2>&1`; no glob reads the path, so
   brackets, braces such as `{a,b}`, stars, a leading `-` and such characters in the
   checkout path all work, checked on Node 22.23.2), then the marker line `# pdd-autopilot-
   NONCE: KIND I exit CODE` (NONCE a random hex per run, KIND `vectors`, `formal`,
   `linked`, `control-vectors` or `control-formal` (below), I the file's index in its
   kind). All files of the run go through one awk filter, so the
   bound is for the whole log: after 4 MB of output it passes the marker lines, TAP
   result and location lines cut to 300 characters for 1 MB more, and once `# pdd-
   autopilot: output cut after 4194304 bytes`; it prints no other line, and keeps only
   the last top-level TAP summary line of each key and the last plan line of the current
   file, which it prints just before that file's marker. So the log stays near 5 MB, also
   with many summary-shaped lines, and each file's counts stay true. The engine reads the
   log in 1 MB parts, line by line (bounded memory), and keeps for each file the last TAP
   summary before its marker (`tests`, `pass`, `fail`, `skipped`, `todo`), the exit code,
   and at most 20 failing tests of its kind with their files. A file passes with exit 0,
   at least one test and 0 failures; it fails with a non-zero exit or a failure (also a
   non-zero exit with no summary: the file did not load); a file with exit 0 and no test
   has no result. A kind is the sum of its files; a kind with a failed file fails, and a
   kind with a file with no result cannot substantiate a positive claim. A positive
   aggregate never hides a missing file. A runner line counts only when the line
   starts with the phrase (the queue and the install print them so; a failing test's
   TAP text, which quotes such a phrase in an indented YAML line, is a test failure); the
   suite's runner lines follow the same rule. A kind with exit 0 and 0 failures passes; a
   non-zero exit or a failure fails (a `# fail 0` with a non-zero exit fails too). A
   runner failure (a missing file marker, a run that died or was killed or stopped by T1,
   exit 86 or 127, a queue runner line) starts again in the same checkout, at most twice;
   then the run is "not run (REASON)", which names the files with no result. The claims against the run, for each kind:
   - A failure is red: "Autopilot ran the KIND tests that this change touches (FILES) at
     head H: F of N failed: TEST (FILE). The Evidence line says KIND=CLAIM."
   - A pass with no file of the kind left out and no skipped or todo test: a `vectors`
     claim must be `pass`, with the same counts when it gives counts; a `formal` claim
     must be `proved` or `bounded`. Else red (the claim is not true), with the true value
     to write.
   - Not run, a file of the kind that the engine does not run, or a skipped or todo test
     (a skipped obligation never supports a pass or a proof; an all-skipped formal run is
     not proved): a positive claim (`vectors=pass`, `formal=proved` or `bounded`) is red:
     "… Autopilot could not check it: REASON. Fix the cause, or write KIND=not-run." A
     non-positive claim is fine. The engine's runner is not the issue: this red alone
     never ends a healthy job. It is red at most once per job and kind (`notRunReds`),
     and never when no repair is left. After that the engine never repeats the claim: it
     writes that kind itself as `KIND=not-run (Autopilot could not check: REASON)` in the
     Evidence line of the merge or would-merge note and in the history line (the job's
     receipts), so metrics count it as not run, never as pass, and one `pdd` report
     (`autopilot-core`, code `replay-not-run`, `shipped: true`) goes to the report owner,
     once per job. A later run that checks the kind clears this (`unchecked`), and so does
     a later head that has no file of that kind.
   The merge note has one line for each kind with files: `- Replay tests (Autopilot's
   run at H): STATE (P/N): FILE STATE (P/N), …` (each file with its own result, at most
   20, then "and N more") and `- Formal tests (…)`, `- Not run by Autopilot
   (REASON): FILES` for other runners, or `- Replay and formal tests (Autopilot's run):
   none changed`.
   **Replay files that import a changed module, and the control (#3227 fix 2):** the run
   also has each `*.vectors.test.*` file of the head that imports a changed code module
   by a relative path (a `from`, `import(` or `require(` string that resolves to the
   changed file; the candidates come from `git grep -z -l -F` of the module's file name;
   at most 100; a file that is already in the set is not repeated). Their KIND is
   `linked`. A failure is red like the others ("Autopilot ran the replay tests that
   import a changed module (FILES) at head H: …"), a file with no result is only shown,
   and no Evidence claim counts them (the agent's `vectors=` counts the changed files and
   the files that read a changed scenario). The note has `- Replay tests that import a
   changed module (Autopilot's run at H): …`. A code file is a changed file with a code
   extension (`.js`, `.mjs`, `.cjs`, `.ts`, `.mts`, `.cts`, `.jsx`, `.tsx`, `.py`) that is
   not in a `test`, `tests`, `__tests__`, `spec` or `fixtures` folder and not named
   `*.test.*` or `*.spec.*`. When the PR changes code files and the run has `vectors` or
   `formal` files, the same command runs those files a second time, as the control: in a
   second clean checkout of the head (`worktrees/N-control`) in which each changed code
   file has its content at the merge base (`git merge-base origin/BASE HEAD`; a file that
   the merge base does not have is removed). The control KINDS are `control-vectors` and
   `control-formal`, with their own markers; a lost control file is a runner failure
   like any other. A base merge makes a new head, so the control runs again against the
   new merge base. The note has `- Control (the same tests on the merge-base code of
   CODE, merge base B): F of N failed (the tests show the change)`, or `… all N passed
   (the tests do not show the change)`, `… no file failed, but N of M gave no result`, or
   `… not run (REASON)`. A control failure is
   never red. When every control file passed, the Evidence line has a positive claim of
   the kind (`vectors=pass`, `formal=proved` or `bounded`), and a Path line uses path a,
   c or e (a behavior change; with path b the contract stays, so a pass on the base is
   expected), the engine asks once per job, and only while a repair is left: "Autopilot
   ran the replay and formal tests of this change (FILES) on the merge-base code of the
   changed code files (CODE, merge base B): all N pass there too, so they do not show
   the change. Add a test that fails on the merge-base code and passes at this head.
   When the base already has the fix (for example after a base merge), keep the base's
   code, keep only what the base does not have, and say so in the PR body." The record
   keeps the linked and control results.
   **The evidence record (#3227 fix 3):** each merge check writes one engine record per
   head, `logs/N-evidence-HEAD.json` (`pdd.core-evidence.v1`, written only when it
   changes): the PR's Runtime lines and claims, the T01 result with the saved rows that
   it read (Story, pass, current, time, tests, failed checks, refusal codes, sent; at
   most 50) and the merge base read (commit, passing Stories, error), the replay and formal run with
   each file's result, the full suite (state, exit, log name, failed tests), CI and review
   states, the PR's Evidence claim and the honest Evidence (above), and **one "Not
   covered" list (B3)**: what the engine did not check at this head, for example each
   "not run" Runtime line, the consumers above 10 that no check covered, a reader or
   merge-base read error, each replay or formal file that it does not run, a kind that it
   could not check, a control that did not run, a missing suite command, and each cut
   input (B2). The reviewer's summary has the list (`- Not covered: …`, or `nothing that
   Autopilot knows of`). The agent's lines are
   claims that the engine checks; the record is the engine's own. The reviewer's brief
   names the record's path and a short summary. The merge and would-merge note take
   their engine lines from it and name it, and the PR body gets one engine block between
   `<!-- pdd:autopilot-core:evidence:start -->` and `<!-- pdd:autopilot-core:evidence:end -->`
   (replaced in place, before the follow-ups section; its lines never read as a
   Runtime, Path or Evidence line). When the PR body outside fenced code blocks, code
   spans and HTML comments has no GitHub closing keyword for `#N` (`close`, `closes`,
   `closed`, `fix`, `fixes`, `fixed`, `resolve`, `resolves` or `resolved` before `#N`,
   `REPO#N` or the issue URL) and does not mark `#N` partial (`Refs #N`, `Part of #N` or a
   `Not fixed yet:` line), prepend `Fixes #N` right before that engine block so a person's
   merge on GitHub closes the issue automatically. The record stays after END: the local cleanup keeps
   `*-evidence-*.json` like the logs, because worktrees and job files go.
4. Any red finding: stop the other checks, but first keep the partial results (#3227 fix
   4): while the engine's replay run (T04) still runs, the merge check waits for it (it
   takes minutes; at most 30 minutes after the first red, `redAt`), so its reds join the
   same round; and a full suite that is still running gives the failed tests that its
   log already shows (`failingTests` of a bounded log tail) as one more red line: "The
   full test suite (still running at head H) already shows failed tests: TEST (FILE), …".
   A red suite's line names its failed tests the same way. `failingTests(text, limit=20)`
   is exported, the one parser of failed tests (group 3 uses it too): `[{name, file}]` in
   log order, each test once (the same name with the same file, or with no file on one
   side; the known file stays). TAP `not ok N - NAME` lines at any depth: a failure stays
   open until its `location:` line, the next `ok` or `not ok` line or 12 lines, so one name
   in two files is two tests; a `# TODO` or `# SKIP` directive is no failure; `\#` and `\\`
   unescape. Spec-reporter results use each run's own `ℹ fail N`, `ℹ todo N` and
   `ℹ suites N` summary, plus its `✖ failing tests:` section. Keep failed counts from
   every run in a combined log; a later passing run does not erase an earlier failure.
   The section's failure rows give test names. The leading tree can repeat a failed child
   as a failed `describe` or `suite`; those suite rows are not additional failed tests.
   When a run has no suites, its failed parent `test()` rows can add counted test names.
   Never use an unmatched suite tree row as a test. A complete summary with `fail 0`
   means that run has no spec failure, even when TODO or skipped tests have `✖` lines. A
   partial spec log without the summary does not prove a failure. When no TODO or skipped
   tests ran, the final duration suffix gives the test name; earlier duration-like text and
   `# TODO` or `# SKIP` stay in the name. When TODO or skipped tests ran, report a test name
   only when its line is clear: a reason after the duration is not a failure, while a
   duration-shaped reason or title is ambiguous. If a summary confirms failures but the
   rows do not identify all failed tests clearly, report the remaining failure count as
   unclear; do not guess a test or file. A root-level fileless `✖` inside the
   `✖ failing tests:` detail is not a new reporter block and does not close that detail:
   it has no test name by itself, while a later `test at FILE:LINE:COL` and failure row
   still give a file-backed test. This exception is only that root fileless `✖`: a later
   root `▶` or `✔` starts the next reporter block. An unpaired fileless row stays
   represented only by the summary's unclear count. The `test at FILE:LINE:COL` line
   before a spec row gives its file. The
   **repair budget** (option B): repairs go on
   while they make progress. The findings of a round are each review must-fix (P1 and P2)
   and each other red line. Two findings are the same when they name the same `file:line`
   (3 lines of tolerance) with a similar cause (2 shared words and a quarter of the words,
   or 40% of the words; the words leave out paths, so two bugs at nearby lines of one file
   differ), or, with no
   place, when nearly all their words agree; a hex commit name does not count. After a
   repair, compare the findings with the last round. Stop (END `checks-red`, the END text
   names the rule and lists the findings, then `What the path checks read: …` with the
   quote of each path red among them, from `paths.quotes`, so a person sees a false red
   at once) when (a) a finding of the last round is still
   there, (b) a finding of an earlier round came back, or (c) the job has used `repairs`
   (the safety cap, default 6). A round that fixes all its findings and gets new, different
   ones goes on (the #2574 pattern: each repair fixes the last P2 and the reviewer finds a
   new P2), to a PASS or the cap. Else start one repair job (it clears `review`, `suite`,
   `vectors` and `coverage`, so every check runs again, also at the same head), count it and start its quiet
   clock. The job saves the last 8 rounds (`rounds`).
5. Wait while CI, review or suite is not green. CI is green when the head has at
   least one check and none is pending. CI is `none` (the full suite and the fresh
   review decide alone) only in a repository with no PR CI: no head of this job ever had a
   check (`ciSeen`), no workflow file of the base tip can run on the PR head
   (`workflowRunsOnPr`: its `on:` has `pull_request` or `pull_request_target` whose branch
   filter admits the base, whose `types` (when given) include opened, synchronize or
   reopened, and whose `paths` / `paths-ignore` admit one of the PR's changed files (`git
   diff --name-only origin/BASE...HEAD`); or `push` whose branch and path filters admit the
   job branch and the changed files; GitHub's globs `*`, `**`, `?` and `!`; a workflow with
   only `repository_dispatch`, a schedule, a release, closed PRs, other paths, tags or
   pushes to other branches, such as the PDD App's dispatch file, is no PR CI), and no
   required status checks on the base. The workflow files come from `git show
   origin/BASE:.github/workflows/NAME` after one fetch per tick (no API call). The safe side
   counts as CI: a read error, a file whose `on:` the reader cannot read (no `on:`, a
   flow map over several lines), and more than 50 workflow files. And 10 minutes passed
   since `prAt`. **A head with no check at all may be a conflict** (GitHub runs no
   `pull_request` workflow while the PR conflicts with its base): then the tick fetches the
   base and runs `git merge-tree --write-tree --name-only --no-messages origin/BASE HEAD` in
   the job worktree; exit 1 (a conflict) starts the agent conflict update (`conflictFix`,
   debate B, outside the lane, with the conflicting file names), not a CI wait. A new head that has no run yet (for example after a
   refresh) waits for its CI. A pending check still waits, as long as it takes; save `progress`
   first. **The owner wait (#3239):** a green PR whose path checks have unchecked files
   does not enter the lane. Its last error is `the merge waits: WAIT` (step `bindings`
   with an unreadable base `pdd-bindings.json`, else `owners`). The wait is not
   progress, so when nothing changes for the quiet period it is a step stop (step 1),
   never an END: main's file is not the issue, so there is no strike and no note on
   the issue, the stop files the one deduplicated PDD report (`bindings-unreadable` or
   `owner-unreadable`), and the loop guard holds the issue after 3 such stops in 24
   hours. When the base tip moves, the path checks read it again.
5a. **Runtime resend (#3241, rule B5), one function `runtimeResend`.** When the PR
   body has a "not run" Runtime line and no FAIL or unclear Runtime line, the tick reads
   once for each agent head the saved checks of the job worktree since the job started (`resendableStoryChecks` of the [runtime client](runtime-client.prompt.md)
   with `root` the job worktree and `since` the job start; saved as `runtimeWait {head,
   state, stories, neverSent, noVerdict, failed}`). A check is sent once more when it
   was **never sent** (held in maintenance, busy, stopped before sending) or was **sent
   with no verdict and no failed check** (an AI provider failure), and only for a Story
   that a "not run" line names (a "not run" line with no Story stands for all; #3227
   per-Story lines). A Story with a failed check is never sent again, and then nothing
   is sent for that head. Nothing to send:
   step 2 applies as usual. Else, when everything above is green, the job holds this
   step before the merge lane:
   - **Wait.** At most every 10 minutes (or sooner when a known future `until` arrives,
     with at least a 5-second floor) it reads the free interpreter health
     (`checkRuntimeHealth`: one `GET /v1/capacity`, no check, no AI call). While the
     answer is maintenance, the job waits: it writes no new line and files no report,
     it holds no slot (it runs no process), and each tick counts as progress, so the
     quiet rule never ends it. The claim heartbeat goes on. Other jobs and intake go on
     as usual.
   - **Send once.** When the answer is not maintenance, the engine itself runs `pdd
     test --json STORY…` for those Stories in the job worktree, with no agent (process
     role `runtime`, watched by the process rule like the suite). It sends at most once
     for each agent head.
   - **Outcome**, for each sent Story from the rows of the last JSON summary line of its
     log (a row names its Story by its base name): all its rows passed is a PASS, a
     failed row or a failed check is a FAIL, anything else (no row, no verdict, a
     refusal, a run that was stopped or died) has no verdict. The engine rewrites the
     line of each sent Story (one line with no Story becomes one line for each sent
     Story), the verdict first and the Story in the parentheses: `Runtime: PASS (STORY,
     P/T checks)`, `Runtime: FAIL (STORY, F of T checks failed; pdd test sent again by
     Autopilot)` or `Runtime: not run (STORY: the check that Autopilot sent again gave
     no verdict)`; the lines of other Stories stay. The Evidence part `runtime=` and the
     saved runtime state follow all lines: `pass` when every line is PASS (T01 in step 3
     then checks the cover, as for every PASS claim), `fail` with a FAIL (the Runtime
     gate sends it to a repair), else `not-run`, with kind `runtime` and code
     `no-verdict` when a sent Story had no verdict (step 2 files its one report). The
     next tick reads the PR again from step 1.
   - **Backstop.** When the maintenance lasts 12 hours from the first read that saw
     it, the job stops waiting: the line of each Story becomes `Runtime: not run (STORY:
     maintenance since HH:MM UTC)` (the time of that first read), the runtime cause is `{kind: runtime,
     component: pdd-test, code: maintenance}`, step 2 files one report, and the merge
     check goes on.
   - **Audit.** Before the first rewrite for a head, the job saves the agent's own
     Runtime lines, its Evidence line and its runtime result as `runtimeOriginal
     {head, lines, evidence, runtime, engine}` (`engine` holds the lines that the
     engine wrote); the history line of the job keeps it.
   `runtimeResend(ctx, job, pr)` returns `{state, hold, head, stories, neverSent,
   noVerdict, failed, since, until, line}`: state `none`, `waiting`, `sending`, `pass`,
   `fail`, `no-verdict` or `maintenance`, and `hold` true while the merge check stops
   here; other steps (for example the #3227 line checks) read this result. A repair
   and a new agent result clear `runtimeWait`. The PR body is written back with a
   PATCH of the PR; a failed PATCH waits for the next tick.
6. **Merge lane** (one final step per repository). A green PR (CI green or none,
   review PASS, suite pass) enters the lane. The lane is the label `pdd:merge-lane` on
   one open PR, shared by every machine through GitHub (`issues?state=open&labels=…`,
   PRs only). Because that label search index can lag behind both `POST` and `DELETE` or
   merge writes, every holder read (before `POST`, on the post-`POST` readback, and in
   the pre-merge race guard) reconciles the listed PRs and any local `phase: pr` jobs in
   `lane.state: final` against each candidate's consistent issue record (`GET issues/N`):
   a candidate whose `GET issues/N` is closed or lacks `pdd:merge-lane` (right after a
   merge, a lane-exit `DELETE`, or a person removing the label) is excluded (and clears
   `job.lane` on a local `final` job); another local `phase: pr` job in `lane.state:
   final` whose `GET issues/N` shows the label or fails transiently counts as held so two
   local PRs never enter `final` in the same tick under `POST` list lag; this PR itself
   (when already in `final`, after `POST`, or in the race guard) counts as held when `GET
   issues/PR` shows the label on the open PR or when the list includes it and `GET
   issues/PR` fails transiently. Any machine clears a remaining stale holder (a closed or
   merged PR, or a core issue (`pdd/core-N-…` branch) with no live claim that is no local
   final-step job) and an orphan one (not a core PR). **One winner on every tick:** the
   lowest open holder number; every other PR removes its own label (a failed DELETE throws
   and the next tick tries again) and waits. When another PR holds the lane, or an older
   green PR of this machine (claim order, `started`) waits, the PR waits: `lane {state:
   waiting, holder, since, heldSince}`, and its quiet clock starts again each tick
   (`progress.running`), so waiting never ends a job and never counts as a refresh; a
   wait for the same holder longer than the quiet period sends one `stuck` alert. Else
   the PR adds the label and runs the reconciled holder read (if neither the list nor
   `GET issues/PR` shows the label on this open PR, try again next tick). The holder is
   in the final step: `lane {state: final, since, waited}`. A repair (which also clears a
   stale waiting state, as a new head does), an END (of any kind, before its other steps),
   a hand-over, a person's stop and an observe validation leave the lane (remove the
   label); a merge closes the PR. Active `phase: pr` jobs in a tick advance with any
   `final` holder first and then in lane-priority order (`lanePriority`, then `started`,
   then `issue`) so claim order holds when two PRs turn green on the same tick, and when
   the lane frees during a tick (a merge or any lane exit) with no local PR in `final`,
   the tick advances waiting PRs at once in that same order (at most once per waiting job)
   instead of waiting for the next timer tick. **Race guard:** right before `gh pr merge`
   the PR runs the reconciled holder read and the compare again; it merges only as the
   lowest open holder with `behind_by` 0.
   The order (debate B L6, C1, C2): a PR that came back from a conflict update
   (`lanePriority`) goes first, then claim order; a PR whose changed files meet a live
   reservation of another PR (this machine's job files, or the `reserved {files,
   until}` of other core PRs' claim records) waits for it. `nativeMergeQueue` is the
   hook for GitHub's merge queue (decision D4, later): today it returns null.
   **Final step, conflicts (debate B 5.4; `laneConflict` is the one place of the
   conflict rule).** Fetch the base and the branch and run `git merge-tree --write-tree
   --name-only --no-messages origin/BASE HEAD`. Exit 0 is clean; any code other than 0
   or 1 leaves the decision to the refresh merge. On exit 1, merge with
   `merge.conflictStyle=diff3` in the job worktree and classify each conflicted file. A
   conflict never goes to a repair. Mechanical (fixed in the lane, no agent, the review
   kept as `mechanical`, never a repair): M-a a hunk that differs only in derived
   `Generated from P (sha256: …)` header lines (the header is then recomputed with
   `promptHeaderHash` from the merged prompt P, so approval metadata does not change it);
   M-b pure inserts (one copy of identical text, else the base side
   first); M-c adjacent hunks that do not overlap (both applied); M-d a JSON file merged
   3-way (union of keys, a key changed on both sides is not mechanical, arrays that
   both sides only extend keep both additions). The fixed merge is committed and
   pushed; the suite and CI run on it; red checks on that head start an agent update
   instead of a repair. Anything else (the same lines edited on both sides, an add/add
   of one path, a missing side, binary) is an **agent conflict update** outside the
   lane: leave the lane, count `conflictExits`, start a `conflict` job in the job
   worktree with the three-sided hunks and the rules (merge the base, change only lines
   inside the conflict hunks, add no files, run the focused tests; an add/add with
   disagreeing specs ends with code `duplicate-design`). It is a base update, not a
   repair, when the PR's changed lines outside the conflict files and its file set stay
   the same; else it uses a repair (with none left, END `checks-red`). The PR then goes
   first in the lane. C2: at the 2nd conflict exit the PR reserves its conflict files
   for an hour (job and claim record); C3: the 3rd ends the job `base-moving`.
7. The head must contain the current base tip (`compare/BASE...HEAD`, `behind_by` 0).
   When the base moved, refresh natively in the job worktree (L3): reset to the job
   head, merge `origin/BASE` (identity "PDD Autopilot", no hooks, no signing), push the
   branch and take the new head; this is not a repair, and the suite and CI always run
   again. A base move after the first refresh of one lane entry (a person's merge) is
   a recheck: at the 3rd recheck the PR leaves the lane with no penalty and goes first
   again (L4); rechecks never count as conflict exits. There is no other refresh cap.
   **Review keep (debate B 5.5)**: F is the SHA-256 of the `+` and `-` lines of `git
   diff -U0` from the merge base (without derived header lines), in path order. R1:
   the same F and file set before and after keeps the PASS review (`kept`). R2: a scoped
   check (`review.scoped {reason, detail, files}`: a short reviewer that reads only that
   part and answers "does the result keep both changes and break neither?") when the
   base changed a line within 10 lines of a PR hunk, or a prompt that owns a file of the
   PR, or after a conflict update that changed F only in the conflict files. R3: a
   fresh full review for any other change of F.
   Run `checkAutopilotBase` of the [automatic base](autopilot-base.prompt.md). A
   read failure ("could not verify", "unavailable", "retry") waits and is saved as the
   last error with step `base-check` (a quiet wait is a `pdd` step stop, as for #2892);
   another refusal ends `base-check`.
8. Read the winning claim again: another live owner means hand-over and no merge; a
   claim that is not confirmed as this job's waits (step `claim`). Post one merge comment on the PR for this head: `CI: green (N check(s))` or
   `CI: none (…)`, the suite, the lane (`Merge lane: final step`, with the queue
   minutes when it waited), the review (`Review: PASS from a fresh reviewer`,
   `Review: PASS (kept after a clean base refresh, same change)`, `Review: PASS (kept:
   the lane fixed only mechanical conflict hunks)` or `Review: PASS (a scoped check
   after REASON, on top of the earlier full review)`), the PR's Runtime
   line, the parsed evidence
   (`Evidence: runtime=pass (11/11); …` in the fixed key order, or `Evidence: none`)
   and the base check,
   with the marker `<!-- pdd:autopilot-core:merge:HEAD -->`. Then
   `gh pr merge PR --repo REPO --merge --match-head-commit HEAD`. A failed merge
   waits for the next tick (step `merge`). A confirmed merge clears `job.lane` and marks the
   lane freed at once (before issue/label writes and local cleanup, so a retained job file
   never blocks waiting PRs), closes the issue when it is open, removes `pdd:working` and
   `pdd:would-merge` when present, cleans up locally (see END) and records `merged`.
   In mode `observe`, the same comment starts `Autopilot would merge this PR (observe
   mode): every check passed for head HEAD. It stays open and ready for review;
   Autopilot does not merge it.` with the marker
   `<!-- pdd:autopilot-core:would-merge:HEAD -->`. Then a draft PR is marked ready
   (`gh pr ready`; a refusal only warns), this machine's claim comment and
   `pdd:working` go, the issue gets the label `pdd:would-merge` (visible to every
   machine), the result counts (`produced`), and local cleanup records `would-merge`
   with the evidence: validation passed, not merged. The ready rule of every machine
   skips an issue with `pdd:would-merge`, because its PR waits for a person; a person
   removes the label to have it built again.

## END

`END(cause)` takes `{kind, component, code, text, detail}`; kinds are `runtime`
(as the agent says it; the [report owner](autopilot-reports.prompt.md) keeps only no
verdict, interpreter error, server incompatibility and a server-side internal error as
Runtime's, and makes a refusal of our input, such as a lint, interface or binding
refusal, a PDD report), `pdd` (CLI error, crash, claim error) and `job` (the agent did not do the
task, no progress, red checks, a hang of the change). A quiet merge check step is a
step wait, never an END ([Stop owners](#stop-owners)). It stops the job's processes and saves phase
`ending`, then, resumable step by step on later ticks:

0. Each tick counts one try. After 6 tries, or 24 hours in phase `ending`, send one
   `stuck` alert through `ports.alert` (its own tried and need: finish the END by hand), clean up locally with
   outcome `abandoned` and stop retrying.
1. When the job has a PR, read it first: a merged PR finishes as merged, never as END.
   A PR that cannot be read is retried on 2 more ticks, then the END goes on.
   Read the claim. When another machine holds it live, hand over. A resumed END or
   release reads the claim again right before each write on the issue (the release's
   claim comment and label delete, the END's dependency link and comment, and the
   labels): when another machine owns it now, hand over and write nothing on the
   issue.
2. For a `runtime` or `pdd` cause, file or count one report through the
   [report owner](autopilot-reports.prompt.md) with the repository's settings
   (`report` mode, `runtimeRepo` and `runtimeOwner`).
3. A `runtime` or `pdd` cause whose report has a GitHub reference **waits for the
   report, not for a person**. Loop breaker first: when an earlier END comment on
   this issue has a blocked-by marker with the same fingerprint and that report is
   now closed, the cause came back after its fix, so a person decides. Otherwise
   link the issue natively: `POST repos/REPO/issues/N/dependencies/blocked_by` with
   the report's issue id. A refused link (for example across repositories) leaves
   the hidden marker in the END comment as the only record; the ready rule reads it.
4. Post one issue comment with the cause text (one final period), kind and code (the kind
   is the report owner, `reportKind`, so a binding refusal says `pdd`), the
   log file name (`Log: \`NAME.log\` on this machine`), the
   branch and PR, `Blocked by REF` when a report has a reference (`#N` in the
   same repository), a draft note naming `pdd autopilot report`, and either "ready
   again when REF closes" or how to retry (remove `pdd:stuck`). Every comment with a
   report reference carries `<!-- pdd:core-blocked-by:REF:FINGERPRINT -->`. A hidden
   marker `<!-- pdd:autopilot-core:end:N:JOB-ID -->` makes a retry after an uncertain
   post find the earlier comment instead of posting twice.
5. Remove `pdd:working` (an absent label is fine). Add `pdd:stuck` for a `job` cause,
   for a `runtime` or `pdd` cause without a GitHub report (draft, off or over the
   daily limit: nothing to wait on), and for a loop.
6. When the job has an open PR, leave it open: mark it draft (`gh pr ready PR --undo`;
   a refusal only warns) and comment the cause on the PR once, with the marker
   `<!-- pdd:autopilot-core:end-pr:N:JOB-ID -->`. A failing GitHub call retries on the
   next tick; after 3 failed tries the note is skipped with a warning.
7. Only then clean up locally (below). Record `ended`.

Local cleanup, after END, a merge, a hand-over or a person's stop: first capture and
stop the build, review, suite, vector and active Runtime replay processes, then confirm
that every saved process identity is gone. If a status read fails, keep the saved part
and still ask the job runner's cleanup port for proof. The failed read is not proof of
cleanup and does not prevent an independent cleanup attempt. Keep the job record and
every worktree for retry if cleanup cannot confirm every saved identity, the inventory
is incomplete, or ownership is uncertain. Do not remove logs, branch or history. Only after
confirmed cleanup, remove every `worktrees/N…` folder of the issue (as in intake); remove every
`logs/N-…` file except the `.log` files that the END comment and the history name;
append the history line. Each step has its own error boundary and only warns.
`jobs/N.json` goes last only after cleanup is confirmed. A merge also deletes the local branch; other outcomes keep it, because the
agent's commits may exist only there.

## Status

`coreStatus({state, settings, guard}, {root, reportRoot, now, fs})` returns text from local
files only: the engine line (mode, repository, folder, base, agent), the slot line
(`B of R slots busy`, no-progress limit, repairs, report mode, opt-in label), the
guard's machine line when the launcher gives one (`guard`, for example `Machine:
share 50% (default) of 10 cores and 16 GiB · slots min(4, 5 cores ÷ 2, 8 GiB ÷ 3 GiB) = 2
→ 2 (automatic) · … · new work: held (memory pressure)`), the pause
line (`New jobs paused until TIME (H h): …` or `No pause: N no-result end(s) in a row …`), the CI line
while `ciDown` is set (`CI does not start: …`), one line per job (`#N build running 12m (log …)`, `#N PR #P at SHA: review …,
suite …`, with `; merge lane: final step`, `; merge lane: waiting for PR #P since TIME`,
`; Runtime: waits for the interpreter maintenance since HH:MM UTC (until HH:MM UTC); no
slot` or `; Runtime: the check that was not sent runs again`, `#N ending: …`), one line per step wait
(`#N waits: OWNER stop CODE: TEXT; next try after TIME (try K)`, with `; report REF` when one was filed), one line per
held issue (`#N held since TIME: TEXT; it goes on after a new engine version or a person's comment on the issue`), one
line per issue that cools down (`#N cools down until TIME (owner OWNER): TEXT`), the last 5 results (`#N ended TIME: cause`,
with ` (owner OWNER)` when the line has one; strike lines are not results) and the count
of local report drafts.

## Text on GitHub

Every comment that this engine posts (review verdict, merge note, END comment, PR
notes) first becomes public text, above its trailing hidden marker lines only (a
marker never changes): an absolute path (`/a/b…` or `~/a/b…`, two parts or more,
after a space, quote, bracket, `=` or `,`) keeps only its file name; this machine's
host name becomes `this machine`; and the local user name (the last part of HOME, or
`ports.user`) becomes `[user]`. A name is replaced only as a whole name (not inside a
longer word or dotted host name). Texts never name another machine: a
hand-over says "another machine holds the claim now". A cause sentence ends with one
period, never two. Then it goes through [secret redaction](secret-redaction.prompt.md) and is cut to at
most 20,000 characters; hidden markers at the end stay whole. A saved `lastError` is
redacted and cut to 300 characters. The claim comment holds only the claim record,
with the machine id.

## Machine settings

`state.label` (saved by `start --label`), `state.mode` (saved by `start --mode`) and
`state.decisions` (saved by `start --decisions`) win over `pdd.json` for this repository
on this machine. The launcher applies them; `coreStatus` takes `sources: {engine, label,
mode, report, decisions}` (`machine` or `pdd.json`) and names the source: `engine core
(this machine: pdd autopilot start --engine core)` or `engine core (pdd.json
autopilot.engine)` when `engine` is given (the launcher gives none, so the line says
`engine core`), `only issues with LABEL (this machine)` or `(pdd.json)`, `mode M
(this machine)`, `reports R (this machine)` and `decisions D (this machine)` (the Jobs
line has `; decisions D` after the reports); mode `observe` adds `(every check, no
merge)`.

## Ports

`gh(args, {input})` and `git(args, {cwd})` return `{code, stdout, stderr}`; GitHub
REST calls use `gh api --include --method M ENDPOINT [--input -]`. Also `now()`,
`fs`, `root`, `reportRoot`, `env`, `version` (the PDD version), `listIssues()`,
`trusted(row)`, `agentReady()`, `warn(text)`, `alert({issue, kind, text, tried, need, update})`,
`machine` (`{room, priority(role)}` of the [machine guard](machine-guard.prompt.md); absent: no
room check and the job runner's default priority), `untestedStories(tree)` (default
`findTests` of the preflight), `runtimeHealth()` (default `checkRuntimeHealth({env})`) and `resendChecks({root, since})`
(default `resendableStoryChecks` with `env`) of the runtime client, and the replaceable `jobs`
(`start`, `read`, `snapshot(part)`, `cleanup(part)`, `cpu`, `hangs`). `cleanup(part)` owns
the fresh process capture and stop, and returns `{confirmed}`. A separate status read or
snapshot is not cleanup proof. `owners(numbers)`, `heartbeat(job)` and `checkBase(input)`
with the native defaults named above.

## Dependencies

- [File owner lookup](file-owner.prompt.md): required for `findOwners`, `resolveOwners`
  and `promptHeaderHash` (M-a derived prompt headers).
- [Headless job runner](agent-job.prompt.md): required for job start, outcome, capture and cleanup.
- [Machine guard](machine-guard.prompt.md): required for `slotCount` (the slots) and
  `GUARD` (the cleanup limits).
- [GitHub dependency reader](issue-dependencies-github.prompt.md): required for the
  winning-claim read (owners port), `refreshClaimHeartbeat` and `takeoverLimited`.
- [Automatic base](autopilot-base.prompt.md): required for `checkAutopilotBase`.
- [Report owner](autopilot-reports.prompt.md): required for `fileReport` and drafts.
- [Shared full-suite queue](test-suite-queue.prompt.md): required context for the
  `pdd workflow suite` job.
- [Secret redaction](secret-redaction.prompt.md): required for suite log tails.
- [Runtime client](runtime-client.prompt.md): required for `savedStoryEvidence` (the
  saved checks of T01, with `comparisonRoot` and `withTests`; the merge base read also
  with `anyRoot` and `limit`), `resendableStoryChecks` and `checkRuntimeHealth` (the
  Runtime step 5a).
- [Runtime preflight](runtime-preflight.prompt.md): required for `findTests` (Stories and
  their tests, `excludeFixtureProjects`), `captureSource` (Story footprints), `gitFiles`,
  `readPrompt`, `promptRefusal` and `interfaceBlocks`.
