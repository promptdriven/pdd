# Autopilot launcher

Own `src/autopilot-launcher.mjs`. Export module functions `runAutopilotLauncher(input, ports)`,
`tickAutopilot(stateFile, ports)`, `withAutopilotModeLock({cwd, env}, action, ports)` and `resetAutopilotCircuitBreaker({cwd, env, mode}, ports)`. This launcher connects a
repository on this machine to the [core engine](autopilot-core.prompt.md): headless agent jobs with no coordinator
chat, no Herdr session, no parking and no AI scheduling. The core engine owns the jobs, claims, merge check, repair
and END. The launcher owns the machine state, the user timer, the tick lock, doctor at start, status, the commands
below, and the one-time [move from the removed full engine](#the-move-from-the-full-engine). It adds no approval,
merge, quota-reset or interactive route of its own. Preserve existing setup, workflow and interpreter behavior.

`runAutopilotLauncher` accepts command doctor, start, stop, status, add, release, report, intake or check-base, cwd, packageRoot,
env, issues (argv operands), and optional runs, checks, engine, label, share, autoUpdate, mode, report, decisions, intake, agent,
pool, all and json. Return
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

`start --label NAME` saves `state.label`, which replaces the core's `label` setting. `start --mode auto|observe|off`
saves `state.mode`, which replaces the core's mode in the tick, the start's off check and status (source `this
machine`); it never writes `pdd.json` (unlike `pdd autopilot observe`). `start --report file|draft|off` saves
`state.report` the same way. `start --decisions ask|decide` saves `state.decisions` the same way: it replaces the
core's `decisions` in the tick and status (`decisions MODE (this machine)`). `start --intake off|shadow` saves
`state.intake`; the core tick gets `intake` from it
(`intakeMode` of the [intake cards](autopilot-intake.prompt.md): `off`, `shadow` or `active`; `state.intake` wins over
`autopilot.intake` in `pdd.json`, and `off` is the default). A blank label, or another
value of `--mode`, `--report`, `--decisions` (`Use --decisions ask or --decisions decide.`) or `--intake` (`Use --intake off, --intake shadow or --intake active.`), returns exit
code 2 with its usage line before any effect. `start --share PERCENT` (#3231, `shareOption`) saves `state.share`, a
whole percent from 1 to 100: the part of this machine's CPU and memory that Autopilot may use (default 50 when none is
saved); a later start without it keeps it, and pdd.json never sets it. Another value returns exit code 2 with `Use
--share with a whole percent from 1 to 100, for example --share 70 (the default is 50).` before any change. `start --agent NAME`
selects `codex`, `claude`, `gemini` or `agy` and returns exit code 2 with `Use --agent codex, claude, gemini or agy.`
for any blank or other name before any change. Hidden `start --pool PATH` (kept for internal local-folder pool fixtures) validates the login pool with `loadLoginPool` of the
[Cloud accounts and login pool](login-pool.prompt.md) and saves `state.poolPath` (`off` or `none` saves `"off"`, disabling
automatic pool discovery; a blank or invalid pool file returns exit code 2 with its validation line before any
change). When Cloud Accounts is active for the saved agent provider (`isCloudAccountsActive({env, poolPath, provider: agent.kind})`) and no explicit local `poolPath` overrides it, ticks wire `selectCloudPoolLogin` and `exhaustCloudPoolLogin` (`weeklyStopPercent: 100`, Stick-Until-100%, disposable `0700` Codex overlay and Claude OAuth/gateway env, `Waiting on AI quota until <wake_at>` on `all_cooling`) automatically with zero `--pool` flag; when main jobs use a non-enrolled or non-Cloud agent (`agy`, `gemini`, or un-enrolled local `codex`/`claude`) while Cloud Accounts has an enrolled `codex` or `claude` login and intake is enabled, `selectPool()` returns `null` so main jobs keep `state.agent` directly while `selectPool({allowedKinds: ["codex", "claude"]})` leases the enrolled Cloud login for intake card and auto-improve checks. `start --auto-update release|main|off` (#2710) saves `state.autoUpdate` (default `release` when unset; another value returns
exit code 2 with `Use --auto-update release, --auto-update main or --auto-update off.`); after each enabled core tick,
run `maybeAutoUpdateAutopilot` of [Autopilot self-update](autopilot-update.prompt.md) under the machine admission lock
when no job is publishing or merging, and include `autoUpdateStatusLine` in status. Optional `--runs` and `--checks` are positive safe integers with no product maximum; save explicit values, and
remove them when a start omits them.

## Automatic continuation custody

The state file is `ROOT/ID.json`, where ROOT is `ports.stateRoot` or `~/.local/state/pdd/autopilot` and ID is the
first 20 hex characters of the SHA-256 of the Git root. Save it atomically (a temporary file and a rename, mode 0600).
A new state that a start creates gets `engine: "core"`, because only a state that an older pdd saved can need the
move. The core state folder is the state file path without `.json` plus `-core`; the machine report folder is
`core-reports` beside the state files.

Start, stop, release and mode controls serialize on one admission lock (`acquireRunLock` of the workflow runner on the
admission folder); a wait that times out returns `Timed out waiting for the current Autopilot operation; retry.`
`withAutopilotModeLock({cwd, env}, action, ports)` runs a settings write (`pdd autopilot auto` and the others) under
that lock for this checkout's state; outside a Git repository it runs the action without the lock, and another Git
failure returns `Autopilot settings could not verify the Git repository; retry.` After a successful action it replaces
the saved control revision, so a tick or start that read the old revision does not publish stale state.

## Doctor and start

Dispatch doctor to [the doctor owner](autopilot-doctor.prompt.md). A start first keeps the Git-folder validation
above, then reads only the saved state. **It asks for an opt-in label first unless intake is active:** when neither `--label`, the machine
label nor `autopilot.label` in `pdd.json` names a label, the effective intake mode (`--intake`, saved `state.intake` or `autopilot.intake` in `pdd.json`) is not `active`, and the mode (the machine mode from `--mode` or saved, else
the core mode of `pdd.json`) is not off, return
exit 1 with exactly `Autopilot did not start: it works only on the issues that you mark with an opt-in label. Run pdd
autopilot start --label pdd:autopilot, then mark issues with pdd autopilot add N (or add the label on GitHub). Nothing
was started or claimed.` No doctor, state write, timer, tick, claim or GitHub call happens. When the effective intake mode is `active` and the mode is not `off`, start also requires a `codex` or `claude` login for sandboxed read-only intake card checks: either the selected single agent has kind `codex` or `claude`, at least one `codex` or `claude` login is enrolled in Cloud Accounts (when `--pool` is not `off`), or at least one non-paused signed-in `codex` or `claude` login exists in the configured `--pool`; otherwise refuse before writing enabled state with `Active intake needs a codex or claude login for sandboxed read-only card checks; add a codex or claude login with pdd accounts add, pass --agent codex or --agent claude, or use --intake off --label pdd:autopilot.` Then it checks whether the
caller requested an explicit account or login-pool override (`--agent`, `--pool`, or an explicit caller `CODEX_HOME`,
`CLAUDE_CONFIG_DIR`, `GEMINI_CLI_HOME` or `ANTIGRAVITY_APP_DATA_DIR` that differs from the saved `launchProfile`).
Without an explicit override it resolves the saved agent profile (`savedProfile`); with `--agent` or `--pool` it
targets the requested agent or first ready non-credit/non-reset pool login (refusing before doctor or state writes if every login in `--pool` is flagged with `credits` or `allowReset`, and with an explicit config-folder override it runs doctor in the
caller's environment without pinning the old saved profile). It runs that doctor with the selected invocation
environment and injected ports, before any start state write, admission lock, timer change, claim or GitHub mutation.
No directory or lock is created by that resolution. On a required failure return the complete doctor report unchanged.
After a pass, use that invocation environment for the startup checks, and print the doctor's WARN lines first in the
start message. A doctor pass alone grants no approval or merge authority.

A start then, in this order:

1. Takes the admission lock to read and, for a new state, save the disabled state (`enabled: false`, no timer).
2. Reads the repository settings ([Autopilot settings](autopilot.prompt.md)). When no machine mode is set (`!machineMode(state)`) and the repository mode is `off` (including an external repository with no `pdd.json` when no `--mode` override is set), start returns exit 0 with its
   message and `Choose observe or auto with pdd autopilot observe or pdd autopilot auto.` When a machine mode is set (`observe`, `auto`, or `off` which continues to step 7 to disable and stop the timer), start continues without requiring `pdd.json`.
3. Reads the repository metadata (`gh repo view --json nameWithOwner,defaultBranchRef`) and saves `repo` and
   `defaultBranch`. A different saved repository refuses.
4. Refuses an `autopilot.quietMinutes` below 2 times the core timer (20): `Autopilot did not start:
   autopilot.quietMinutes is N; it must be at least 20 (2 times the 10-minute core timer). Nothing was started or
   claimed.`
5. Selects the automatic base, checks `gh auth status`, and selects the agent: without an explicit account or pool
   override it keeps the saved profile when one is saved (refuse when it is unavailable) and refuses a silently changed
   saved profile with `The saved coordinator profile cannot be verified.`; without a saved profile, or when `--agent`,
   `--pool` or an explicit caller agent config folder overrides the saved profile (#3230), it saves the newly verified
   agent, its definition HOME, the kept environment (`HOME`, `PATH`, the agent config folders, the XDG and D-Bus session
   values, `PDD_STATE_DIR`, `PDD_ACCOUNTS_URL`, `PDD_CLOUD_URL` and the shared queue variables `PDD_SUITE_QUEUE`,
   `PDD_VM_SUITE_LOCK` and `PDD_SUITE_CONCURRENCY`; never credentials or the whole environment), `launchProfile` from the new
   profile binding, and `poolPath` when `--pool` is set, removes legacy `ownerLaunch`, clears stale `pausedUntil`,
   `pausedHours`, `streak` and `poolOut` in `core.json` (plus `clearPoolCooldowns` when switching accounts or pools),
   and adds an `Account changed from OLD to NEW.` or `Login pool: PATH (N login(s)).` note to the start message.
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
6. Reads the machine guard before the core tick, so existing work can advance without waiting for another
   repository's intake. When the core has a ready issue, its `machine.reserve()` port takes the machine admission
   lock at `ROOT/autopilot-machine-admission.lock`, where ROOT is the shared state folder beside every repository's
   state file. Under that lock it reads the guard again, then holds the reservation only while the core checks room,
   saves a new job record and starts its agent. This serializes the shared room check and job admission across
   repositories; two ticks cannot use the same free machine slot. The release happens before unrelated core work,
   such as issue scans, claim heartbeats, merge checks and reports. A busy reservation waits up to 5 seconds; it
   holds only new intake with `intake held: the machine admission is busy; the next tick retries.` Running work
   continues. This lock is separate from the repository admission lock used by start, stop, release and state saves.
7. At the end, saves the tick's ETag cache, compacts the GitHub ledger to its last 2 hours and removes the lock.

The core tick reads the core settings from this checkout's `pdd.json` and replaces label, mode and report with the
machine values when saved, and sets `labelRequired: true`, so the core claims no issue while no label is set (status
says so). Mode off stops the intake card jobs and returns `Autopilot is off.` Otherwise it selects the automatic base,
computes the machine GitHub budget (`githubBudget` of [GitHub calls](github-calls.prompt.md) with all ledgers of this
machine and the settings' `github` value), and calls `tickCore` with this launcher's counted `gh` and `git` process
port, its issue list (`queryIssues` with the saved ETag pages: a list of more than one page is read in full only every
6 hours, and between full reads the tick reads the issues changed since then), its trust rule for authors
(`trusted`: the owner, the core trust list, or write, maintain or admin permission, read once per login), the
read-only Codex limits as `agentReady` (only `limited` holds intake; 97% weekly stop protection applies) and, when a
multi-harness login pool is configured (`loadLoginPool(...).configured`), `selectLogin(opts)` (forwarding optional `allowedKinds` to `selectPoolLogin` and caching per-`allowedKinds` key until `exhaustLogin` clears it) and `exhaustLogin` from the
[login pool](login-pool.prompt.md), the package version, an `alert` port that sends
one alert of the given kind for the issue through this machine's [alert destination](autopilot-alerts.prompt.md) with
the core's cause, tried and need, the core state folder, the report folder, `tickMinutes` (the installed
interval), `etags` (`p.etags`, persisted right after `tickCore` as well as in the tick `finally` block so conditional `If-None-Match` `304 Not Modified` reads work across poll ticks), `preflightCheck` (calling `runDefaultPreflightCheck({tool, command, cwd: state.cwd, env: p.env})` from the core engine for Bucket 2 tool health probes unless overridden by `ports.corePorts`), and on native ticks `wake` (`node src/autopilot-launcher.mjs --start-scan-wait IDENTITY`) so a finished child worker triggers an immediate follow-up tick with zero slot idle gap. When using native alerts (`!ports.sendAlert`), before `tickCore` runs, the tick runs `runAutopilotAlerts({action: 'retry', ...})` so open `failed` or newly-configured `not-configured` incidents of this repository from earlier ticks are retried once credentials recover. Before the core tick, the [machine guard](machine-guard.prompt.md) reads this machine once
(`readMachineGuard({cwd, runs: state.runs, repoRuns: pdd.json autopilot.runs, machineRuns, share, jobs, readyLogins})`, where
`machineRuns` is the highest saved `runs` across active repositories in `stateRoot` (so `--runs N` above 4 on one repository lifts whole-machine `machineSlots` consistently in both `coreGuard` and `status` while keeping sibling repositories at their own `slots`), `share` uses `state.share` or the active machine `share`, `readyLogins` is passed when locally known from `readLoginPoolSummary` unless `state.poolPath === 'off'` (and omitted when Cloud pool count is unknown locally so single-login and lease-only hosts keep default `autoSlots`), and
`jobs` comes from `inspectMachineJobs(stateRoot, ports)`: it scans every saved `*-core` folder under `stateRoot`
including disabled repositories, counting `busySlots` for enabled repositories and still-running slot-holding jobs (excluding phase `ending` or `released`, interpreter maintenance `runtimeWait`, and unresumed `poolExhausted` PR waits) with
live child processes (`pid > 1` with matching wrapper token, reading `/proc/PID/cmdline` first on Linux before `ps`) for disabled repositories so disabling a repository while workers finish never hides active machine
load, and inventories live child roles (`build`, `repair`, `review`, `suite`, `vectors`, `runtime`, `intake`) across
`*-core/jobs/*.json` and `*-core/intake/jobs/*.json` without inflating issue-slot count; tests replace the guard with
`ports.machineGuard`, #3231). The machine
port includes `reserve()`: only when ready intake exists, it takes the shared machine-admission lock, refreshes this
guard object from the current job files, and returns a release function. The core calls it immediately before its
room check and releases it after all new job records and agents are started, so the snapshot stays current while the
core makes its admission decision without blocking unrelated core work. The core
settings come from `readCoreSettings(cwd, fs, {auto, runs: state.runs, hardwareSlots: guard.hardwareSlots})`, so this machine's `start --runs N` reaches
the core and a machine without it gets its automatic slots; the core gets the guard as its `machine` port (the room
check and each job's priority). Tests may replace core ports with `ports.corePorts`. Afterwards, under the admission lock and only while
still enabled, it saves the issue-list cache, the base fields, `intakeNote` when present, `mode: "observe"` (recording `circuitBreakerForcedObserve: true` when `latest.mode` was not already `observe`) plus `circuitBreaker` when `tickCore` newly tripped the post-merge safety circuit breaker (#3484; cleared with `circuitBreakerClearedAt = now` saved in both `stateFile` and `core.json` on every `pdd autopilot start` — dropping breaker-forced `state.mode` when `--mode` is omitted so `"mode": "auto"` in `pdd.json` resumes `auto`, and clearing stale `circuitBreaker` banners on `--mode observe` — and via `resetAutopilotCircuitBreaker` on `pdd autopilot auto|observe|off`, which also clears machine `observe` overrides on `auto` and `off`), `nextTick` (now plus `timerMinutes`) and `core: {at,
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
- `processes()`: one local read of this machine's process table (`ps -A -ww -o pid= -o ppid= -o pgid= -o rss= -o uid= -o
  lstart= -o args=`; on Linux without `ps`, `procTable` of the move owner reads `/proc`); `signal(pid, name)`: `process.kill`, where an ended process is no error; `sleep(ms)`.
- `commonDir`: the real path of this checkout's Git common folder; `coreJobs()`: the issue numbers of the core's job
  files; `cwdOf(pid)`: exact local process working-directory evidence (`/proc/PID/cwd` on Linux — falling back to `readlinkSync` with trailing ` (deleted)` stripped when the directory was unlinked — or `lsof` on macOS),
  null where it cannot be read. The worker move asks it only for rows owned by `process.getuid()` and rechecks a null
  result against the same PID/start/command identity; `save(journal)`: saves `retiredFull` in the state file under the admission lock; `samePath`; `now`.
  Tests may replace any of them with `ports.movePorts`, or the whole step with `ports.moveToCore`.

When the move is complete, save `movedState` of the move owner (engine core, the journal with its line, no
full-engine key) under the admission lock, and print the move line once through `ports.notice` (default: stderr,
which is the timer's log). A move that is not complete returns its message as the tick result. Status shows `Moved
from the full engine at ISO: LINE` for 7 days after the move; before it, for a machine that ran the full engine,
`This machine moves from the full engine to the core engine at its next tick` with the last error or the waited
ticks, and `no new work starts before that.`

## Stop, status and the other commands

Export `requestAutopilotCompletion({ cwd, env }, ports)` for capacity handoff ticks: resolve the Git checkout root and its saved launcher state file; return `{ state: "inactive" }` when Autopilot is not enabled, run one guarded `runTick` otherwise, and return `{ state: "busy" }`, `{ state: "reconciled" }` or `{ state: "unknown" }`.

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
`FILE: saved state unreadable`. Each line is independent, and the timer reads run from the caller's folder. `runAutopilotLauncher` itself performs zero file writes on disk across all `status` forms (`status`, `status --all`,
`status --json`, and `status --all --json`, computing run costs in memory with `captureCosts`; at the outer
[CLI entrypoint](pdd-cli.prompt.md), `--json` also bypasses `#3424` pre-dispatch `syncOwnedUserSkills`). Both
**Status --all** (text, which checks saved repository modes and user timers) and **Status --json** (JSON, with or without
`--all`, which reads local state files and local OS/Git observations only — making zero `gh`, Herdr, OAuth, agent, or
network calls, and skipping `systemctl` and `launchctl` timer probes) include read-only machine observability: (1) one
machine-level `machineGuard` summary (`guard.line` in text, structured `machineGuard` object in JSON, passing locally
known `readyLogins` and active `share`/`runs`/`machineRuns` identically with `coreGuard`), (2) role-grouped `activeJobs`
(`{build, repair, review, suite, vectors, runtime, intake}`) and `suiteQueue` (`readCheckStatus`), (3) local-disk-only
`loginPool` summary (cached `accounts-state.json` entries when Cloud Accounts is enrolled, or local `loadLoginPool` +
`readPoolCooldowns` excluding `paused` and credit/reset-guarded logins from `ready` — failing closed with state `invalid`
and `readyLogins: 0` when an explicit or default local pool file fails `loadLoginPool` validation, and returning
`not-configured` with `readyLogins: null` only when no pool file is configured: `ready`, `cooling`, `paused`,
`reauth_required`, `5H`/`7D` usage and reset times with `null` shown as `?` and never fabricated `0%`, or `unavailable`
when no local Cloud cache exists), and (4) read-only core `conversion` summary wired from `summarizeConversionDrops()` over saved
`*-core/history.jsonl`, `*-core/intake`, and `core-reports` drafts, and (5) read-only `recurringFlakes` summary aggregated from saved `*-core/flakes.jsonl` ledgers via `summarizeRecurringFlakes` of [Autopilot regression detection](autopilot-regressions.prompt.md) (symlink-safe, fail-safe when absent; included as `recurringFlakes` in **Status --json** and rendered as a concise `Recurring flakes (7d, >=3): ...` line in **Status --all** text only when `recurring.length > 0`). **Status --json** preserves top-level local cost
report fields alongside `costs` and `repositories`, exiting `0`.

**Add** creates the `pdd:autopilot` label when it is missing and adds it to each named issue of this repository (an
issue of another repository returns exit 2): `Marked N issue(s) with pdd:autopilot.`

**Release** delegates `pdd autopilot release ISSUE` to `releaseCoreJob` of the [core engine](autopilot-core.prompt.md#release)
with this repository's state file, resolved `state` (`machine` defaulting to the host name when unsaved), counted
`gh` and `git` ports (purpose `claims`), `ports.corePorts`, and a `releaseClaim(machine, ref = ISSUE, onMutate)` callback to `releaseRunClaim` of the
workflow runner (keeping the workflow run lock, worker and check-custody guard, Herdr chat cleanup and local allocation
release with the runner), and returns its `{exitCode, message}` unchanged. Under the shared `STATE.lock` tick lock,
release checks ownership across `machineIdOf(state)` and `state.machine`, immediately stops any live local core job
processes without waiting for a later tick, frees any held `pdd:merge-lane` label without closing PRs or deleting
worktrees, logs or branches, removes `pdd:working` and `pdd:stuck`, appends one `released` history record and removes
`jobs/N.json`.

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

## Dependencies

- [Autopilot core](autopilot-core.prompt.md), [Autopilot reports](autopilot-reports.prompt.md) and
  [intake cards](autopilot-intake.prompt.md): required native generation and verification context for the core tick,
  core status, release, and the report and intake commands.
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
- [Shared full-suite queue](test-suite-queue.prompt.md): required context for `releaseCheckCapacity` and `readCheckStatus`.
- [Codex limits](codex-limits.prompt.md) and [multi-harness login pool](login-pool.prompt.md): required native
  generation and verification context for the read-only usage read and ordered multi-harness login rotation.
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
- [Autopilot self-update](autopilot-update.prompt.md): required native generation and verification context for safe
  between-tick global `pdd` and skill updates.
- [Autopilot regression detection](autopilot-regressions.prompt.md): required for `parseFlakeLedger`,
  `summarizeRecurringFlakes`, and `formatRecurringFlakesLine` in read-only status observability.
