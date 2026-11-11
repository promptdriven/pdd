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
record is simply dead. There is no "uncertain custody" state.

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
- `startAgentJob({id, dir, cwd, command, args, input, env, hung}, ports)` writes
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
- The wrapper starts `command args` in `cwd` with the input file as stdin and the
  log as stdout and stderr (append). When the child ends, it writes
  `{code, signal, at}` to the exit file with a temporary file and a rename. On
  SIGTERM, SIGINT or SIGHUP it stops the whole job: it sends SIGTERM to its own process
  group (the child and every process the child started, for example `npm ci` under
  `sh`), waits 2 s (a timer that keeps the wrapper alive, also when the direct child
  exits first), writes the exit record (the child's code and signal when it exited,
  else the stop signal; best effort), and then sends SIGKILL to the whole group, itself
  last. A failed exit-record write or descriptor close never skips that SIGKILL. A
  process that treats the first SIGTERM as "stop gracefully" and waits never survives
  as an orphan. A process that left the group (its own `setsid`) is out of reach.
- **The hung-command watch** (only with `hung`). An agent waits for each command that it
  runs; a command that does nothing (a stalled `npm install`, a test that waits forever)
  keeps the whole job silent until the core's quiet rule stops the job. So the wrapper
  stops only that command, and the agent sees it fail and can go on. Every `every` ms it
  reads the job log size and change time and the process table once (`ps -A -o
  pid=,ppid=,time=,etime=,command=`, 5 s timeout; a failed read skips the round):
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
- `agentJobHangs(job)` returns the parsed hang list of `job.hangs` (only the objects in
  it), or `[]` when the file is absent, unreadable or not a list.
- `readAgentJob(job, ports)` returns `{state, exit, result, log}`; a missing job record
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

Default `alive(pid, token)` is true only when signal 0 reaches `pid` and the
process command line (`ps -o command= -p PID`) contains `token`. A pid that the
system reused after a restart belongs to another command, so it never counts as
the job and is never stopped.

## Dependencies

Node child_process, fs and path supply native effects. Native tests cover this module
with scripted agents; no real agent is called.
