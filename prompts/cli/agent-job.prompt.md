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
- `startAgentJob({id, dir, cwd, command, args, input, env}, ports)` writes
  `dir/ID.input` (the prompt, mode 0600) and `dir/ID.spec.json`, then starts
  `node src/agent-job.mjs --wrapper SPEC` detached in its own process group, with
  `env` and no inherited stdio, and returns at once with
  `{id, pid, token, log, exit, result, input, started}`. A spawn that fails later
  (an `error` event: a cwd that is gone, EAGAIN, ENOMEM) writes the exit record
  `{code: 127, signal: null, at, error}` and is never an uncaught error; the job then
  reads as exited with no result. `token` is the spec path;
  `log`, `exit` and `result` are `dir/ID.log`, `dir/ID.exit.json` and
  `dir/ID.result.json`. `id` must match `[A-Za-z0-9._-]+`.
- The wrapper starts `command args` in `cwd` with the input file as stdin and the
  log as stdout and stderr (append). When the child ends, it writes
  `{code, signal, at}` to the exit file with a temporary file and a rename. On
  SIGTERM, SIGINT or SIGHUP it stops the child and still writes the exit record.
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
  true only when the job was alive; it returns false and sends nothing otherwise.

Default `alive(pid, token)` is true only when signal 0 reaches `pid` and the
process command line (`ps -o command= -p PID`) contains `token`. A pid that the
system reused after a restart belongs to another command, so it never counts as
the job and is never stopped.

## Dependencies

Node child_process, fs and path supply native effects. Native tests cover this module
with scripted agents; no real agent is called.
