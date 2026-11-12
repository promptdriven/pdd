# Headless agent jobs

Own `src/agent-job.mjs`. It starts one headless process (a coding agent or a plain
command) that keeps running after the caller exits, and it reads the outcome later
from files only. The [Autopilot core](autopilot-core.prompt.md) uses it for build,
repair, review and full-suite jobs. It makes no GitHub call, no model call of its own
and no scheduling decision. Processes, clock and liveness reads use ports with native
defaults.

## Why files

The tick that starts a job exits within seconds; the job runs for up to hours. A
later tick, or a tick after a restart, must learn the outcome without a parent
process. So the job leaves its whole state in files next to each other: a spec, an
input, a log, an exit record and the agent's result. A dead process with no exit
record is dead. Cleanup may stay unconfirmed while saved process or custody evidence
is uncertain; those records let a later tick retry without a live controller.

## Public contract

- `agentCommand(agent, {model}={})` returns `{command, args}` for `agent.kind`
  `codex` or `claude`, using `agent.command` or the kind as the program:
  - codex: `exec --json --dangerously-bypass-approvals-and-sandbox -c features.multi_agent=false [--model M] -`
  - claude: `-p --output-format stream-json --verbose --permission-mode bypassPermissions [--model M]`
    (a stream of events, so the log grows while the agent works; the result is the
    result file, not the output)

  Both read the prompt on stdin and have full access, like the post-merge auditor
  launch in [the audit owner](autopilot-audit.prompt.md). Another kind throws
  `Error("Autopilot core jobs need codex or claude")`.
- `jobEnvironment(env)` returns a copy of `env` without keys that would join the
  caller's own agent, Herdr or coordinator session: `CLAUDECODE`, `CLAUDE_CODE_*`,
  `CLAUDE_PID`, `CODEX_THREAD_ID`, `CODEX_SANDBOX*`, `HERDR_*`, `PDD_AGENT_SESSION`
  and `PDD_AUTOPILOT_CONTEXT`. Account settings such as `CODEX_HOME` stay.
- `startAgentJob({id, dir, cwd, command, args, input, env, hung, custodyRoot}, ports)` writes
  `dir/ID.input` (the prompt, mode 0600) and `dir/ID.spec.json`, then starts
  `node src/agent-job.mjs --wrapper SPEC` detached in its own process group, with
  `env` and no inherited stdio, and returns at once with
  `{id, pid, token, log, exit, result, input, hangs, started}`. A spawn that fails later
  (an `error` event: a cwd that is gone, EAGAIN, ENOMEM) writes the exit record
  `{code: 127, signal: null, at, error}` and is never an uncaught error; the job then
  reads as exited with no result. `token` is the spec path;
  `log`, `exit`, `result` and `hangs` are `dir/ID.log`, `dir/ID.exit.json`,
  `dir/ID.result.json` and `dir/ID.hangs.json`. `id` must match `[A-Za-z0-9._-]+`.
  `hung` is optional: `{after, every, cpu}` (milliseconds, milliseconds, CPU seconds),
  saved in the spec; it turns on the hung-command watch below. The core passes it for
  agent jobs only (15 minutes, 30 s, 2 s), never for a plain command such as the suite.
  `custodyRoot` is optional. Only a caller that will remove a known disposable
  worktree passes its root; the runner records its absolute path. `cwd` alone is
  never a custody root: a job may run in a person's persistent source tree.
- `startAgentJob` also takes `priority` (`{nice, qos, cpus, taskset}` from the
  [machine guard](machine-guard.prompt.md)) and saves it in the spec. Every job
  runs at the lowest priority (#3231), the child and not the wrapper: the wrapper only
  waits, and it must answer a stop at once on a busy machine. `jobCommand(spec,
  platform)` gives the command and arguments that the wrapper starts: first, on macOS
  with `qos` (default `utility`) and an executable `/usr/sbin/taskpolicy`,
  `/usr/sbin/taskpolicy -c utility COMMAND ARGS…` (utility QoS, which also lowers disk
  I/O; not background QoS, which keeps work on the efficiency cores, and no extra disk
  throttle, which kept stopped jobs alive on a busy disk), or on Linux with `cpus` and
  an absolute `taskset`, `TASKSET --cpu-list CPUS COMMAND ARGS…` (Node, `nproc`,
  `cargo`, `pytest -n auto` and Go follow the CPU list, so an agent's own tests use
  Autopilot's share); then, with a nice value (`priority.nice`, default 19) above 0 and
  an executable `/usr/bin/nice`, `/usr/bin/nice -n N` before it. nice, taskpolicy and
  taskset run the command in the same process, so the CPU watch sees the same tree.
  With no nice program the wrapper sets its own nice value with `os.setPriority`
  instead (a failure is ignored), and children inherit it.
- `startAgentJob` also takes `pddCheck` (`{version, cli}`: the engine's pdd version and
  the absolute path of its own pdd, #3177) and saves it in the spec. Right after the
  wrapper starts the child, it asks the agent's own login shell which pdd it finds, the
  way the agent's commands find it (Codex runs each command in one, and a profile can
  put an older pdd first on PATH): `$SHELL -lc` (an absolute `SHELL`, else `/bin/sh`)
  with the job environment and a 20-second limit, printing the marker lines `@pdd-path
  …` (`command -v pdd`) and `@pdd-version …` (`pdd --version`, stderr dropped), so text
  that a profile prints is never read as an answer. It writes the record `{at, found,
  path, version, engine, cli, line}` to `ID.pdd-check.json` (`pddCheckFile(log)`) and,
  when `line` is set, that one line to the log. `pddCheckLine` gives `line`: null when
  the shell finds a pdd of the engine's version, else `pdd path check: the agent shell finds
  pdd X at PATH; the engine is Y; using PDD_CLI (CLI)` or `pdd path check: the agent shell
  finds no pdd on PATH; the engine is Y; using PDD_CLI (CLI)`. A check that fails or
  times out writes nothing. It never changes the job.
- `pddCheck.skills` (`{dir, version, read}`: the engine's own skills folder, its
  `pdd-skills` version and the folders that the agent's tools load by default) is the
  skills check (`checkSkills`): before the shell check, the wrapper reads `pdd-skills:`
  from `FOLDER/pdd-feature/SKILL.md` of each `read` folder. When a folder has another
  version, it writes `{at, found, engine, dir, line}` to `ID.skills-check.json`
  (`skillsCheckFile(log)`) and the one line `pdd skills check: installed skills are X at
  FOLDER, the engine is Y; jobs use PDD_SKILLS (DIR)` (several folders joined with
  "and") to the log. A missing or unreadable folder is no mismatch; it never changes
  the job.
- The wrapper starts `jobCommand(spec)` in `cwd` with the input file as stdin and the
  log as stdout and stderr (append). A group stop can reach the child before the
  wrapper's own signal handler runs: a child that ends by SIGTERM, SIGINT or SIGHUP
  while no stop runs starts the same stop (below), so the whole group still ends after
  the grace time. When the child ends, it writes
  `{code, signal, at}` to the exit file with a temporary file and a rename. On
  SIGTERM, SIGINT or SIGHUP it stops the whole job: it sends SIGTERM to its own process
  group (the child and every process the child started, for example `npm ci` under
  `sh`), waits 2 s (a timer that keeps the wrapper alive, also when the direct child
  exits first), writes the exit record (the child's code and signal when it exited,
  else the stop signal; best effort), and then sends SIGKILL to the whole group, itself
  last. A failed exit-record write or descriptor close never skips that SIGKILL. A
  process that treats the first SIGTERM as "stop gracefully" and waits never survives
  as an orphan. A process that left the group (its own `setsid`) can be captured while
  the wrapper is live, but descendant samples are not a complete ownership boundary.
  `snapshotAgentJob(job)` saves the wrapper and every live descendant as
  PID/start/command identities on `job.processes`. `cleanupAgentJob(job)` captures
  again, asks the wrapper to stop, then terminates saved identities that still match.
  The wrapper starts detached, so its PID is also the dedicated job process-group ID.
  Only a live wrapper whose command still contains this job's token authorizes the
  group SIGTERM. Its handler sends the same group SIGTERM, waits 2 s, then sends the
  group SIGKILL. This group ownership is separate from cwd custody evidence. Cleanup
  also signals saved PID/start/command identities individually, including helpers that
  left the group. Cwd-only suspect identities never authorize a signal. A reused
  wrapper PID fails the live-token check and is never group-signalled. It returns
  cleanup proof. An unreadable
  inventory or a remaining saved identity is unconfirmed. Each live `readAgentJob`
  refreshes this saved snapshot on the job record and in `TOKEN.processes.json`, so it
  survives a tick that returns while the job runs. The wrapper snapshots once
  immediately after it starts its direct child, once more before the first 250 ms
  round, and then refreshes the same cumulative manifest every 250 ms while its child
  runs. Older PID/start identities stay until cleanup, even when a helper reparents.
  A manifest write or inventory failure, or a malformed prior manifest, leaves a
  durable uncertainty marker and cleanup then retains the job. That marker stays for
  the job token even if a later snapshot succeeds: the failed sample could have
  missed a detached helper. A captured live descendant without a valid identity is an
  inventory failure, never a row to discard.

  When the direct child exits, before the wrapper records that exit, the wrapper also
  reads the current user's process table only when the saved spec has an explicit
  `custodyRoot`, and looks only for **unsaved** processes whose current working
  directory is that exact disposable worktree or a directory below it. `cwd` never
  enables this scan. On
  Linux it reads `/proc/PID/cwd`; on macOS it reads `lsof` cwd records. A complete
  inventory that finds a matching process writes a separate durable custody finding
  with the process identities and root. Before it writes the spec or spawns a new
  wrapper, `startAgentJob` saves a custody boundary timestamp in that spec; its
  post-spawn `started` value is never a boundary. A same-user process whose cwd cannot
  be read is retained unless its parseable `ps lstart` second is strictly before that
  boundary's whole-second floor. A same-second process, or one with an unknown or
  unparsable start, stays uncertain. A process proven older cannot be its descendant,
  so its unreadable cwd alone is not a custody finding. This age rule never discards a
  previously recorded identity, and a readable cwd match under the root stays held
  regardless of age. A reused wrapper PID is scanned like any other candidate unless
  it has the exact saved PID/start identity. An incomplete process table, unavailable current-user
  identity or unavailable cwd inventory writes the general uncertainty marker; a later
  cwd scan cannot clear that marker. Cwd evidence is only a reason to retain the job
  and worktree: it never authorizes a signal to that process.

  Cleanup can resolve a custody finding only after it confirms that the saved manifest
  identities are gone, reads a fresh complete process table and cwd inventory, sees
  every recorded suspect identity has ended, and finds no unsaved same-user process in
  the root. A pid with a different start identity is a reused pid. Cleanup records the
  resolution beside the original finding and keeps its history. An incomplete read or
  a live suspect keeps cleanup unconfirmed. A suspect that changes cwd outside the
  root remains held until that same pid and start identity ends; an empty root scan
  alone does not resolve it. Cwd evidence never authorizes a signal to a suspect.
  After it terminates saved identities, cleanup rereads the durable custody and error
  files, confirms the wrapper is gone, and repeats the exact-root scan even when no
  custody marker existed at entry or a prior marker was resolved. A new finding creates
  a marker; a finding after a resolution appends to it and reopens it. A shutdown-time
  error marker or an incomplete fresh scan is unconfirmed.

  A core job from 0.1.28 may have no process manifest. Core may request a bounded
  legacy scan only by passing `ports.legacyCustodyRoot` for a verified core-owned
  disposable checkout, after it matches the old spec's cwd and exit path to that
  checkout and confirms a well-formed exit record.
  The scan requires a complete current-user process table with this reader, proves the
  saved wrapper PID no longer runs this spec, checks the checkout's cwd inventory, and
  checks for surviving members of the wrapper's original process group. Core may pass
  a saved pre-spawn job boundary only when it is known to predate every part spawn;
  it must not guess from a part's post-spawn `started` time. That boundary rules out
  only an unreadable process whose parseable `ps lstart` second is strictly older.
  A same-second, missing or unparsable time stays uncertain. A readable cwd match and
  any previously recorded identity remain held regardless of age. Without a safe
  boundary, an unreadable candidate stays uncertain. Any matching process
  is retained by PID/start identity; an incomplete read stays unconfirmed.
  This path sends no signals. A clear scan permits core to finish removing that checkout,
  but it cannot recover the old manifest: a helper that changed cwd and left the wrapper's
  group before any observation remains outside this historical proof. Report this limited
  legacy clearance as such; do not call it complete historical descendant custody. A
  source tree, shared folder or arbitrary cwd never qualifies.

  This check catches a late detached helper that still uses the worktree. It
  canonicalizes `/tmp` aliases and a deleted cwd through its nearest existing parent.
  It does not prove that no escaped helper exists, and cannot identify a helper that
  changed to a directory outside the worktree before the first complete scan. A caller
  must not pass a persistent source root as `custodyRoot`; a person's shell there must
  not retain an unrelated job. The cwd custody check runs on Linux and macOS only.
  Other platforms keep the existing manifest behavior rather than making every clean
  exit unconfirmed because there is no portable cwd reader.
  The complete process table includes the current reader's PID. `ports.list` supplies
  a scripted table in native tests; each row has a positive PID, start identity, command,
  numeric UID and process state. `ports.cwd(pid, uid, row)` supplies one cwd or throws.
  Native Linux reads `/proc/PID/cwd`; macOS reads `lsof` cwd records. `ports.spawnSync`
  supplies the process-table and `lsof` programs.
  An existing malformed or empty manifest, including an entry without a positive PID,
  a nonblank emitted PID-start identity or a nonblank command, is unconfirmed even
  when an in-memory snapshot exists: it can have missed a later detached helper.
  Cleanup uses that saved snapshot and never relies on a new one after the wrapper exited.
- **The hung-command watch** (only with `hung`). An agent waits for each command that it
  runs; a command that does nothing (a stalled `npm install`, a test that waits forever)
  keeps the whole job silent until the core's quiet rule stops the job. So the wrapper
  stops only that command, and the agent sees it fail and can go on. Every `every` ms it
  reads the job log size and change time and the process table once (`LC_ALL=C ps -A
  -ww -o pid=,ppid=,time=,etime=,command=`, 5 s timeout and a 64 MiB output bound; a
  failed or over-bound read skips the round). Wide C-locale output keeps a long
  command's final `pdd test` or `pdd lint` words visible to the wait exemption:
  - The **helpers** are the processes under the agent at the first round in which the
    log has content (the agent's MCP servers and its own helper processes start before
    its first output). They are never stopped. Before the log has content nothing is
    watched.
  - A **command** is a process under the direct child (the agent CLI) that is not a
    helper, whose parent is not a command, and that started no earlier than 10 s
    before the log's last change: a command that the agent waits on now.
  - A command is **hung** when the log has not changed for `after` ms and the CPU time of
    the command and its descendants grew by less than `cpu` seconds in that time
    (growth of `cpu` seconds or more starts its time again; so does a log change).
  - A **pdd test or pdd lint** is never hung (lead, Nov 11): a command whose process tree
    has a process that runs `pdd test` or `pdd lint` (by a `pdd` or `pdd.mjs` path, or
    as `"$PDD_CLI" test`) is never stopped by the watch. While it waits for Runtime
    capacity or a maintenance window it writes nothing to this log and makes almost no
    CPU, like a hang; its own time limits end it, and the core's quiet rule still sees a
    job that stays silent.
  - For a hung command the wrapper sends SIGTERM to the command and each of its
    descendants, and SIGKILL 2 s later to those that are left. It appends one line to the
    log, `agent-job: stopped a hung command after M min with no output and almost no
    CPU: COMMAND (last output: LINE)`, and adds `{at, pid, command, minutes, last, head}`
    to `dir/ID.hangs.json` (a JSON list of the last 50, written with a temporary file and
    a rename). `command` is the process command line (at most 500 characters),
    `minutes` the silent time (one decimal), `last` the last nonblank log line before the
    stop (at most 300 characters) and `head` the output of `git rev-parse HEAD` in `cwd`
    (5 s timeout), or null. The job goes on; the wrapper never stops the agent CLI or the
    whole job for a hang, and a failed round only waits for the next one.
- Two parts are pure and exported, so their tests check the order and the decisions, not wall time (lead, Nov 11):
  `jobStopper({killGroup, setTimer, writeExit, exit, now, grace})` returns `{stop, exited, finish}` with the stop
  order above (SIGTERM to the group and one timer of `grace` ms, then the exit record, SIGKILL to the group and the
  exit; a second stop changes nothing; a failed write never skips the SIGKILL; a child that ends by a stop signal is
  that stop); `hungRound(memo, {rows, log, now, agentPid, settings})` is one round of the hung-command watch over a
  process table (`memo` keeps the helpers, the reference CPU of each command and the stopped commands) and returns
  the commands to stop, `[{row, sub, minutes}]`. The wrapper and the watch use them with the real process, clock and
  timers.
- `agentJobHangs(job)` returns the parsed hang list of `job.hangs` (only the objects in
  it), or `[]` when the file is absent, unreadable or not a list.
- `readAgentJob(job, ports)` refreshes the durable descendant manifest while the wrapper
  is live, then returns `{state, exit, result, log}`; a missing job record
  is `dead`:
  - `state` is `running` when `ports.alive(pid, token)` is true; else `exited` when
    the exit record parses; else `dead`.
  - `exit` is the parsed exit record or null.
  - `result` is the parsed JSON object at `job.result`, `null` when the file is
    absent, or the string `invalid` when it does not parse to an object.
  - `log` is `{size, mtime}` (bytes and change time in milliseconds) of `job.log`, or
    null when it cannot be read; the core uses it to see progress.
- `agentJobCpu(job, ports)` reads the process table once (`ps -A -o pid=,ppid=,time=`,
  `ports.spawnSync`, 5 s timeout) and returns `{PID: CPU seconds}` for every process
  under the job's wrapper by parent pid (a child that starts its own process group still
  counts), without the wrapper and its direct child (the agent CLI or the suite runner);
  null when the job has no pid or the table cannot be read. Times are `[DD-][HH:]MM:SS[.cc]`.
- `stopAgentJob(job, ports)` sends SIGTERM to the job's process group and returns
  true only when the job was alive; it returns false and sends nothing otherwise. The
  wrapper, the group leader, then ends the group (above): after the 2 s grace no
  process of the group is left.
- `snapshotAgentJob(job, ports)` returns and saves live wrapper descendants. It
  validates the durable manifest first. When a complete process table no longer has
  the wrapper but that manifest is valid, it returns the saved manifest unchanged:
  an exited wrapper cannot add descendants. A missing or malformed manifest returns
  null for a normal current job. An unreadable inventory while the wrapper is present
  also returns null. The post-child-exit cwd check is a separate conservative custody
  check, not a complete descendant inventory. `cleanupAgentJob(job, ports)` returns
  `{confirmed, stopped, killed, remaining}` and adds `legacy` when it used the bounded
  0.1.28 scan. Core must retain its local job record and worktree when `confirmed` is
  false, and save the `legacy` limit when it is true.

Default `alive(pid, token)` is true only when signal 0 reaches `pid` and the
whole C-locale process command line (`LC_ALL=C ps -ww -o command= -p PID`) contains
`token`. A pid that the system reused after a restart belongs to another command, so
it never counts as the job and is never stopped.

## Dependencies

- [Process lifecycle](process-lifecycle.prompt.md): required native process-table, identity and captured-tree
  termination context for snapshots and cleanup. This prompt owns when an agent job captures or cleans up that tree.

Node child_process, fs and path supply native effects. Native tests cover this module
with scripted agents; no real agent is called.
