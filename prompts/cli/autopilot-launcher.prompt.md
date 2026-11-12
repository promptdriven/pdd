# Autopilot launcher

Own `src/autopilot-launcher.mjs`. Export module functions `runAutopilotLauncher(input, ports)`,
`tickAutopilot(stateFile, ports)` and `withAutopilotModeLock({cwd, env}, action, ports)`. This launcher connects a
repository on this machine to the [core engine](autopilot-core.prompt.md): headless agent jobs with no coordinator
chat, no Herdr session, no parking and no AI scheduling. The core engine owns the jobs, claims, merge check, repair
and END. The launcher owns the machine state, the user timer, the tick lock, doctor at start, status, the commands
below, and the one-time [move from the removed full engine](#the-move-from-the-full-engine). It adds no approval,
merge, quota-reset or interactive route of its own. Preserve existing setup, workflow and interpreter behavior.

`runAutopilotLauncher` accepts command doctor, start, stop, status, add, release, report, intake or check-base, cwd, packageRoot,
env, issues (argv operands), and optional runs, checks, engine, label, share, mode, report, decisions, intake, all and
json. Return
`{exitCode, message}`; the CLI owns streams. Outside programs, timer installation, clock and state I/O are injectable
ports; native defaults implement them on macOS and Linux. Tests may inject `checkCapacityPorts` for the shared queue.

## One engine

Autopilot has one engine, the core. `--engine core` is accepted and changes nothing. `--engine full` returns exit
code 2 with exactly `FULL_ENGINE_REMOVED` of [the move](autopilot-retire.prompt.md): `The full Autopilot engine is
removed; Autopilot runs only the core engine. Run pdd autopilot start without --engine.` Any other `--engine` value
returns exit code 2 with `Leave out --engine: Autopilot runs only the core engine.` Both refusals come before any read
or change. `autopilot.engine` in `pdd.json` changes nothing, except that the move reads it to know which engine a
machine ran before.

## Machine state and options

Resolve the Git root, repository identity and package version before a start. Outside a Git repository, start,
stop, status and add return exit code 1 with exactly `This folder is not a Git repository. cd into the repo you want
Autopilot to work on, then run the command again.` and change nothing. Report another Git failure as a Git read
failure; a sign-in message is only for a real sign-in failure. Git translates its messages, so run each Git call whose
error text pdd reads (this Git root lookup and the one in `withAutopilotModeLock`) with `LC_ALL=C` and `LANG=C`.

The state file is `ROOT/ID.json`, where ROOT is `ports.stateRoot` or `~/.local/state/pdd/autopilot` and ID is the
first 20 hex characters of the SHA-256 of the Git root. Save it atomically (a temporary file and a rename, mode 0600).
A new state that a start creates gets `engine: "core"`, because only a state that an older pdd saved can need the
move. The core state folder is the state file path without `.json` plus `-core`; the machine report folder is
`core-reports` beside the state files.

`start --label NAME` saves `state.label`, which replaces the core's `label` setting. `start --mode auto|observe|off`
saves `state.mode`, which replaces the core's mode in the tick, the start's off check and status (source `this
machine`); it never writes `pdd.json` (unlike `pdd autopilot observe`). `start --report file|draft|off` saves
`state.report` the same way. `start --decisions ask|decide` saves `state.decisions` the same way: it replaces the
core's `decisions` in the tick and status (`decisions MODE (this machine)`). `start --intake off|shadow` saves
`state.intake`; the core tick gets `intake` from it
(`intakeMode` of the [intake cards](autopilot-intake.prompt.md); off when none is saved). A blank label, or another
value of `--mode`, `--report`, `--decisions` (`Use --decisions ask or --decisions decide.`) or `--intake`, returns exit
code 2 with its usage line before any effect. `start --share PERCENT` (#3231, `shareOption`) saves `state.share`, a
whole percent from 1 to 100: the part of this machine's CPU and memory that Autopilot may use (default 50 when none is
saved); a later start without it keeps it, and pdd.json never sets it. Another value returns exit code 2 with `Use
--share with a whole percent from 1 to 100, for example --share 70 (the default is 50).` before any change. Optional
`--runs` and `--checks` are positive safe integers with no product maximum; save explicit values, and remove them when
a start omits them.

## Doctor and start

Dispatch doctor to [the doctor owner](autopilot-doctor.prompt.md). A start first keeps the Git-folder validation
above, then reads only the saved state. **It asks for an opt-in label first:** when neither `--label`, the machine
label nor `autopilot.label` in `pdd.json` names a label and the mode (the machine mode from `--mode` or saved, else
the core mode of `pdd.json`) is not off, return
exit 1 with exactly `Autopilot did not start: it works only on the issues that you mark with an opt-in label. Run pdd
autopilot start --label pdd:autopilot, then mark issues with pdd autopilot add N (or add the label on GitHub). Nothing
was started or claimed.` No doctor, state write, timer, tick, claim or GitHub call happens. Then it resolves the saved
agent profile (`savedProfile`), and runs that doctor
with the selected invocation environment and injected ports, before any start state write, admission lock, timer
change, claim or GitHub mutation. No directory or lock is created by that resolution. On a required failure return
the complete doctor report unchanged. After a pass, use that invocation environment for the startup checks, and print
the doctor's WARN lines first in the start message. A doctor pass alone grants no approval or merge authority.

A start then, in this order:

1. Takes the admission lock to read and, for a new state, save the disabled state (`enabled: false`, no timer).
2. Reads the repository settings ([Autopilot settings](autopilot.prompt.md)). Mode off returns exit 0 with its
   message and `Choose observe or auto with pdd autopilot observe or pdd autopilot auto.`
3. Reads the repository metadata (`gh repo view --json nameWithOwner,defaultBranchRef`) and saves `repo` and
   `defaultBranch`. A different saved repository refuses.
4. Refuses an `autopilot.quietMinutes` below 2 times the core timer (20): `Autopilot did not start:
   autopilot.quietMinutes is N; it must be at least 20 (2 times the 10-minute core timer). Nothing was started or
   claimed.`
5. Selects the automatic base, checks `gh auth status`, and selects the agent: the saved profile when one is saved
   (refuse when it is unavailable), else the doctor's selection. Without a saved profile it saves the agent, its
   definition HOME and the kept environment (`HOME`, `PATH`, the agent config folders, the XDG and D-Bus session
   values and the shared queue variables; never credentials or the whole environment). It saves `launchProfile` from
   the profile binding when none is saved, so a later start verifies the same sign-in; a state saved without one
   selects the agent again. A changed saved profile refuses with `The saved coordinator profile cannot be verified.`
6. Saves `startedAt` (ISO time; in auto mode it is the operator action that approves the core jobs' prompt changes),
   `activatedAt` (once), `coordinatorId` and `machine` (once), `enabled`, `nextTick` and a new `controlRevision`,
   then rechecks under the admission lock that no other control changed the state while it started.
7. A machine mode `off` saves the state as disabled with mode off, stops the timer and returns exit 0 with
   `Autopilot core is off on this machine for REPO: mode off is saved and the timer is stopped. To turn it on, run pdd
   autopilot start --mode auto or --mode observe.` (a timer stop failure is named).
8. Starts the user timer and saves `timerMinutes`. A timer failure on a new state restores the disabled state and
   returns `Autopilot timer could not start; enable your systemd user session on Linux or launchctl user session on
   macOS, then retry.` On Linux it checks lingering without changing it and warns how `loginctl enable-linger` keeps
   the timer after logout.
9. Runs the first tick in this process. Its move line (`ports.notice`) goes into the start message. If another tick
    holds the tick lock, arrange one detached follow-up (`--start-scan-wait`) that waits outside every lock, checks
    the same enabled start (folder, repository, coordinator, machine and control revision), then runs one tick.
10. Returns exit 0 with `Autopilot started for REPO in FOLDER. Base BASE. Mode MODE · issues with LABEL · agent ID ·
    pdd VERSION · next tick: ISO. See: pdd autopilot status.` plus the warnings (PATH shadowing, linger, a failed first
    tick).

## Timer and tick

The core tick has no AI call and each job phase needs a tick, so the timer fires every 10 minutes. Start writes the
interval into the timer and saves it as `timerMinutes`; a timer that an older pdd installed counts as 30 minutes. A
named user timer runs this Node script with absolute paths and the saved environment. macOS uses a LaunchAgent
(`StartInterval`, `StandardErrorPath` = state file plus `.log`); Linux uses a systemd user timer (`OnActiveSec`,
`OnUnitActiveSec`) whose oneshot service sets `KillMode=process`. No controller process or polling loop runs between
ticks. **A tick never stops, starts or reloads its own timer** (`launchctl bootout` of the running job would kill the
tick); only start and stop change the timer. Status shows `timer active, every N minutes`, and `(run pdd autopilot
start to use 10 minutes)` when the installed interval differs. Timer priority (#3231): both timer files run Autopilot
at the lowest priority, from the guard's `timerPriority`: the LaunchAgent has `Nice` 19; the systemd service has
`Nice=19`, `CPUWeight=1` below a share of 100 and `CPUWeight=100` at 100, and `MemoryHigh=SHARE%` (the saved share,
default 50).

Executing this module with the timer's state-file operand dispatches `tickAutopilot` for that file. A rejected tick
writes one plain `Autopilot:` line to stderr and sets exit code 1.

A tick:

1. Returns `Autopilot stopped.` for a disabled or missing state.
2. Takes the tick lock (`STATE.lock`). A lock blocks only for a valid live owner; empty, malformed and dead-owner locks
   are reclaimed, and the owner PID is published atomically. A busy lock returns `Autopilot tick already running.`
3. Reads the state again; a start follow-up whose start was superseded returns `Autopilot start was superseded.`
4. Saves a missing `coordinatorId` (a random UUID) and `machine` (the host name) under the admission lock.
5. Runs [the move](#the-move-from-the-full-engine) while the state has no complete move journal. Until the move is
   complete, the tick returns the move's message and starts no core work.
6. Takes the machine admission lock at `ROOT/autopilot-machine-admission.lock`, where ROOT is the shared state
   folder beside every repository's state file. It holds this lock while it reads the machine guard and runs
   `tickCore` through the point where any new job record is saved and agent is started. This serializes the shared
   room check and job admission across repositories; two ticks cannot use the same free machine slot. It then saves
   this repository's tick result under its repository admission lock and releases the machine lock. If it cannot get
   the machine lock within 5 seconds, it starts no core work and returns a deferred tick result; the next timer tick
   retries. This lock is separate from the repository admission lock used by start, stop, release and state saves.
7. At the end, saves the tick's ETag cache, compacts the GitHub ledger to its last 2 hours and removes the lock.

The core tick reads the core settings from this checkout's `pdd.json` and replaces label, mode and report with the
machine values when saved, and sets `labelRequired: true`, so the core claims no issue while no label is set (status
says so). Mode off stops the intake card jobs and returns `Autopilot is off.` Otherwise it selects the automatic base,
computes the machine GitHub budget (`githubBudget` of [GitHub calls](github-calls.prompt.md) with all ledgers of this
machine and the settings' `github` value), and calls `tickCore` with this launcher's counted `gh` and `git` process
port, its issue list (`queryIssues` with the saved ETag pages: a list of more than one page is read in full only every
6 hours, and between full reads the tick reads the issues changed since then), its trust rule for authors
(`trusted`: the owner, the core trust list, or write, maintain or admin permission, read once per login), the
read-only Codex limits as `agentReady` (only `limited` holds intake), the package version, an `alert` port that sends
one alert of the given kind for the issue through this machine's [alert destination](autopilot-alerts.prompt.md) with
the core's cause, tried and need, the core state folder, the report folder and `tickMinutes` (the installed
interval). Before the core tick, the [machine guard](machine-guard.prompt.md) reads this machine once
(`readMachineGuard({cwd, runs: state.runs, repoRuns: pdd.json autopilot.runs, share: state.share, jobs})`, where
`jobs` is the sum of the core's `busySlots` over the core folder of every enabled state file beside this one: the
share is for the whole machine, every repository; tests replace it with `ports.machineGuard`, #3231). The machine
admission lock is acquired before this snapshot and remains held until `tickCore` has saved and started any new jobs,
so the snapshot stays current while the core makes its admission decision. The core
settings come from `readCoreSettings(cwd, fs, {auto, runs: state.runs})`, so this machine's `start --runs N` reaches
the core and a machine without it gets its automatic slots; the core gets the guard as its `machine` port (the room
check and each job's priority). Tests may replace core ports with `ports.corePorts`. Afterwards, under the admission lock and only while
still enabled, it saves the issue-list cache, the base fields, `nextTick` (now plus `timerMinutes`) and `core: {at,
message}`.

Each `gh` call goes through `countGithubCalls` into this repository's ledger in `ROOT/github/`, with its purpose
(`issues`, `claims` or the purpose of its arguments).

## The move from the full engine

A machine whose saved state has no complete move journal (`retiredFull.done`) moves once, inside its next tick
(start runs a tick, so a start moves too). The tick lock is held for the whole move, and the core starts no job until
the move is complete. [The move owner](autopilot-retire.prompt.md) runs the steps and keeps the step journal; the
launcher gives it these ports:

- `gh`: the counted `gh` port (purpose `claims`, 2-minute limit); `herdr`: the old coordinator session
  `pdd-autopilot` (`ports.herdr` when injected; a missing Herdr is `herdr_missing`, so it has nothing to close).
- `listRuns(cancelled)`: the run records of this checkout ([run records](workflow-runs.prompt.md)).
- `cancelRun(run)`: `cancelRun` of the [workflow runner](workflow-runner.prompt.md) with the workflow cleanup ports
  (the `pdd` Herdr session), `claimReleased: true` and `skipMetricsDelivery: true`, so it closes the run's worker chats
  and records the run as cancelled, the move releases the claim itself, and the run's metrics events stay in its outbox:
  the tick leaves no background work behind. `releaseLocal(run)`: `releaseIssueClaim` of the
  [worktree allocator](workflow-worktree.prompt.md) for the run's local issue allocation.
- `releaseSlots()`: `releaseCheckCapacity` of the [shared queue](test-suite-queue.prompt.md) for this state file.
- `processes()`: one local read of this machine's process table (`ps -A -ww -o pid= -o ppid= -o pgid= -o rss= -o
  args=`; on Linux without `ps`, `procTable` of the move owner reads `/proc`); `signal(pid, name)`: `process.kill`, where an ended process is no error; `sleep(ms)`.
- `commonDir`: the real path of this checkout's Git common folder; `coreJobs()`: the issue numbers of the core's job
  files; `save(journal)`: saves `retiredFull` in the state file under the admission lock; `samePath`; `now`.
  Tests may replace any of them with `ports.movePorts`, or the whole step with `ports.moveToCore`.

When the move is complete, save `movedState` of the move owner (engine core, the journal with its line, no
full-engine key) under the admission lock, and print the move line once through `ports.notice` (default: stderr,
which is the timer's log). A move that is not complete returns its message as the tick result. Status shows `Moved
from the full engine at ISO: LINE` for 7 days after the move; before it, for a machine that ran the full engine,
`This machine moves from the full engine to the core engine at its next tick` with the last error or the waited
ticks, and `no new work starts before that.`

## Stop, status and the other commands

**Stop** first saves this repo as disabled (with a new control revision) so a queued tick cannot act even if the
timer cleanup fails, then disables its timer and removes its timer definition, stops the intake card jobs, releases
this state file's check-capacity snapshot, and returns `Autopilot stopped on this machine; the current step can
finish.` Stop removes the owned timer even if the saved installation state is absent or false. Repeated stop is
harmless.

**Status** (in the repository, without `--all` or `--json`) reads local files and the timer only, with no GitHub, Herdr
or AI call: `Autopilot enabled|disabled; timer ...; next tick: ISO|none`, then `coreStatus` with the same machine guard
read (its slots and its machine line: the share and where it comes from, the cores and memory, the slot math, free
memory and pressure, disk, load, priority and `new work: ok` or `held (REASON)`) and the label, mode and
report sources (`machine` or `pdd.json`), then `No opt-in label: Autopilot takes no issue. Run pdd autopilot start
--label pdd:autopilot, then mark issues with pdd autopilot add N.` when no label is set, then the line of
`alertStatusLine` of [Autopilot alerts](autopilot-alerts.prompt.md#status-line) with the saved repository and state root
(an alert that was not delivered; an error adds nothing), then the move line, then the last tick message.

**Status --all** works from any folder, also outside a Git repository. It prints one line for each saved state on this
machine: repository, folder, base, mode (the machine mode with `(this machine)`, else the mode of that folder's
settings, read only when the folder exists and is its Git root; else `unknown (no folder saved)`, `unknown (folder
missing)`, `unknown (not a Git repository)` or `unknown (settings unreadable)`), enabled or disabled, and timer active,
inactive or unknown; a state that has not moved yet adds `moves from the full engine to the core engine at its next
tick`. Without saved state it prints `No Autopilot on this machine.` A state file that is not a JSON object prints
`FILE: saved state unreadable`. Each line is independent, and the timer reads run from the caller's folder. Then it
adds the local cost lines. **Status --json** prints the local cost report as JSON.

**Add** creates the `pdd:autopilot` label when it is missing and adds it to each named issue of this repository (an
issue of another repository returns exit 2): `Marked N issue(s) with pdd:autopilot.`

**Release** releases this machine's own claim on ISSUE through the shared `releaseRunClaim` of the workflow runner
(the run lock, worker and check-custody guard, chat cleanup and local allocation result stay with the runner), and
returns its result unchanged.

**Audit** (`pdd autopilot audit RUN PR`) resolves the saved run with `resolveRun` and calls `auditMerge` of the
[audit owner](autopilot-audit.prompt.md) with that run and PR, through this launcher's counted process port (purpose
`audit`), and returns its result. The core engine starts no audit by itself; #3182 plans to run it after core merges.

**Check base** (`pdd autopilot check-base RUN PR`) resolves the saved run with `resolveRun`, then calls
`checkAutopilotBase` of the [automatic base](autopilot-base.prompt.md) with the saved run and PR through this
launcher's counted process port and its full reply (`{code, stdout, stderr}`), so a refused read names the tool's own
error. It is read-only, does not require a running timer or agent, and supplies the pre-merge guard and post-merge
base audit.

**Report** lists the machine's local report drafts (`FINGERPRINT: title; seen N time(s), last TIME`, then `Send one with
pdd autopilot report send FINGERPRINT.`, or `No local Autopilot report drafts.`); `report send FINGERPRINT` sends one
through `sendReportDraft` of the [report owner](autopilot-reports.prompt.md) with the counted `gh` port. It needs no
repository. Other operands return exit code 2 with the usage line.

**Intake** resolves this repository's state file like status (no admission lock), reads the cards with `readIntake` of
the [intake cards](autopilot-intake.prompt.md) from the core state folder and returns exit 0 with `Intake: MODE on this
machine.` and `intakeText`, or with `--json` the JSON of `{repository, intake, day, cards, running, wouldPick, diff}`.

Another command returns exit 2 with `Use pdd autopilot start, stop, status, add or release.` A thrown error returns
exit 1 with one line; a missing program says `install git and gh, and sign in to your agent, then retry.`

## Admission

Start, stop, release and mode controls serialize on one admission lock (`acquireRunLock` of the workflow runner on the
admission folder); a wait that times out returns `Timed out waiting for the current Autopilot operation; retry.`
`withAutopilotModeLock({cwd, env}, action, ports)` runs a settings write (`pdd autopilot auto` and the others) under
that lock for this checkout's state; outside a Git repository it runs the action without the lock, and another Git
failure returns `Autopilot settings could not verify the Git repository; retry.` After a successful action it replaces
the saved control revision, so a tick or start that read the old revision does not publish stale state.

## Dependencies

- [Autopilot core](autopilot-core.prompt.md), [Autopilot reports](autopilot-reports.prompt.md) and
  [intake cards](autopilot-intake.prompt.md): required native generation and verification context for the core tick,
  core status, the report and intake commands.
- [Post-merge audit](autopilot-audit.prompt.md): required native generation and verification context for the audit
  command.
- [The move from the full engine](autopilot-retire.prompt.md): required native generation and verification context
  for the move steps, the journal and the refusal line.
- [Doctor](autopilot-doctor.prompt.md): required native generation and verification context for first-start checks
  and the shared agent selection.
- [Autopilot settings](autopilot.prompt.md): required native generation and verification context for read-only
  settings resolution and notices.
- [Automatic base](autopilot-base.prompt.md): required native generation and verification context for base selection
  and merge safety.
- [Machine guard](machine-guard.prompt.md): required native generation and verification context for the core slots, the
  room and priority ports, the status machine line and the timer priority keys.
- [Workflow runner](workflow-runner.prompt.md): required native generation and verification context for the admission
  lock, `releaseRunClaim` and `cancelRun`.
- [Run records](workflow-runs.prompt.md) and [cost ledger](cost-ledger.prompt.md): required native generation and
  verification context for run listing and the local cost report.
- [Worktree allocator](workflow-worktree.prompt.md): required native generation and verification context for
  `releaseIssueClaim`.
- [Shared full-suite queue](test-suite-queue.prompt.md): required context for `releaseCheckCapacity`.
- [Codex limits](codex-limits.prompt.md): required native generation and verification context for the read-only usage
  read.
- [GitHub calls](github-calls.prompt.md): required native generation and verification context for the call ledger,
  the budget and the ETag cache.
- [Autopilot alerts](autopilot-alerts.prompt.md): required native generation and verification context for the core's
  alert port.
- [Herdr workspace identity](workflow-herdr-layout.prompt.md): required native generation and verification context
  for `samePath`.
- [Agent adapters](agent-adapters.prompt.md): required native generation and verification context for non-model
  process execution.
- [PATH diagnostics](path-diagnostic.prompt.md): required native generation and verification context for the version
  shadowing warning.
