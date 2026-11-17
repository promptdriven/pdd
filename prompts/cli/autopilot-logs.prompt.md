# Autopilot worker logs

Own `src/autopilot-logs.mjs`. Export `runAutopilotLogs(input, ports)`,
`inspectAutopilotWorkers(input, ports)` and `formatWorkerLogLine(line)`.
Give a person a supported read-only way to list headless Autopilot workers,
inspect a worker's stage, process state, queue position, blockers and saved
evidence, and follow live worker output from the terminal without knowing
internal state folders or touching running jobs.

## Safety and observe mode

Every operation in this module is strictly read-only:

- Never write, create, rename or delete files in the repository, Autopilot
  state folders, validation folders, or user configuration.
- Never approve gates, merge pull requests, claim or release issues, wake
  scheduler ticks, or call GitHub (`gh`). Viewing preserves `observe`, `auto`
  and `off` modes unchanged.
- Check process liveness read-only (`kill(pid, 0)` and `ps` command match on
  the job's `.spec.json` token when present). Never send `SIGTERM`, `SIGKILL`,
  `SIGINT` or any stopping signal to a worker or test-suite process.
- Redact credentials and tokens in every displayed log line, error note and
  path summary with `redactSecrets`. Strip terminal escape sequences so output
  is safe in both interactive terminals and redirected files.

## CLI contract

`runAutopilotLogs({cwd, env, issue, follow, lines, json}, ports)` accepts:

- `issue`: optional issue selector from the positional `[ISSUE]` operand or
  `--issue N` (`17`, `#17`, `owner/repo#17`, or a GitHub issue URL). Passing
  two different selectors, a blank/invalid selector, or `--follow` together
  with `--json` returns exit code `2` with one clear usage message before state
  inspection.
- `follow`: Boolean from `--follow` or `-f`. Requires a selected issue; calling
  `--follow` with no issue returns exit code `2` explaining how to pass an
  issue (`pdd autopilot logs ISSUE --follow`).
- `lines`: positive integer tail count from `--lines N` (default `40`, range
  `1` to `5000`).
- `json`: Boolean from `--json` for structured machine-readable inspection.

Injectable `ports` provide `fs`, `git(args, {cwd, env})`, `now()`, `stateRoot`,
`coreRoot`, `isProcessAlive(pid, token)`, `readSuite({cwd, env})`, `stdout`,
`signal`, `pollMs` (default `250`) and `sleep(ms)`. Resolve the repository root
with `git rev-parse --show-toplevel` under `LC_ALL=C` and `LANG=C`. Outside a
Git repository, return `{exitCode: 1, message: "This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run pdd autopilot logs again."}`.
Derive the state key from `sha256(gitToplevel).slice(0, 20)` under `stateRoot`
(default `<HOME>/.local/state/pdd/autopilot`), reading `<hash>.json`,
`<hash>-core/core.json`, `<hash>-core/jobs/*.json`,
`<hash>-core/intake/jobs/*.json`, `<hash>-core/logs/*` and
`<hash>-core/history.jsonl` plus the checkout's `pdd.json` mode.

## Worker inspection and stage distinction

`inspectAutopilotWorkers` classifies each active job in `<hash>-core/jobs` (and
any active read-only intake card job in `<hash>-core/intake/jobs`) and recent
completed history rows so a person can immediately tell live progress from
waiting or stale state:

1. **Stage**:
   - `build` for initial headless implementation;
   - `repair` (with repair count and PR number when present) so repair passes
     stand out clearly from initial builds and checks;
   - `conflict` for base-branch conflict resolution;
   - `pr-check` on `phase === "pr"`, detailing `review`, `suite`, `vectors`,
     `runtime` check wait, or `merge-lane` state;
   - `ending` or `release-pending` when finishing cleanup;
   - `intake` for read-only intake card workers;
   - `finished` when selected by issue from `history.jsonl` after `jobs/N.json`
     has already completed.
2. **Owned process state**:
   - Inspect each sub-process handle (`job.agent`, `job.review?.agent`,
     `job.suite?.agent`, `job.vectors?.agent`, `job.runtimeWait?.agent`) and
     its `.exit.json` receipt.
   - Report `running (pid N)` when `isProcessAlive(pid, token)` is true;
   - Report `exited (code C)` when `.exit.json` is recorded while the job waits
     for the next scheduler tick;
   - Report `stale (pid N not running, no exit receipt)` when the recorded PID
     is gone without `.exit.json`.
3. **Suite queue waiting versus live test execution versus stale receipts**:
   - Query `readSuiteProgress({cwd: suiteCwd, env})` for PR suite checks.
   - Report `queued (position P in shared test-suite queue)` when `state` is
     `waiting`;
   - Report `running full test suite` (with live validation `logPath`, child
     PID and pass/fail counts when available) when `state` is `running`;
   - Report `stale suite receipt` when a saved suite record has a dead runner
     reason (`recorder_not_running` / ended before reporting) or belongs to an
     older commit than `job.head`.
4. **Blockers and last activity**:
   - Surface blockers plainly: shared test-suite queue wait, merge-lane wait
     (naming the holder PR when present), PDD interpreter maintenance wait, AI
     quota or login-pool cooldown, machine pause, GitHub Actions outage, safety
     circuit-breaker downgrade, hung commands recorded in `.hangs.json`, and
     `job.lastError`.
   - Compute `lastActivityAt` from the newest `mtimeMs` across active worker
     and suite validation logs (falling back to `watch.at` or `started`) and
     show both relative age and UTC timestamp.
   - Collect saved log paths and `<issue>-evidence-<head>.json` files for the
     issue so evidence is directly linked.

## Output modes and live following

- **No issue selected (`pdd autopilot logs`)**:
  Print repository and effective Autopilot mode (noting read-only viewer safety
  when in `observe` mode), active machine-wide blockers if any, a clear list of
  current workers sorted by issue number (showing issue, stage, process/queue
  status, last activity, blockers and log path), recent finished workers when
  present, and the exact command `pdd autopilot logs <issue> --follow` to
  attach read-only to a worker. When no workers or history exist yet, exit `0`
  with a plain empty-state message.
- **Selected issue snapshot (`pdd autopilot logs <issue> [--lines N]`)**:
  Print the worker summary header (issue, mode, stage, owned process state,
  suite/queue state, blockers, last activity, saved log and evidence paths),
  followed by the last `N` human-readable lines formatted by
  `formatWorkerLogLine` from the active log stream(s). If the issue has no
  active worker and no saved history or log in this repository, return exit
  code `1` with a hint to run `pdd autopilot logs`.
- **Readable progress lines (`formatWorkerLogLine`)**:
  Convert Codex `--json` JSONL, Claude `stream-json`, and Gemini/Agy
  `stream-json` records into concise human-readable progress lines (`[session]`,
  `[run]`, `[cmd]`, `[tool]`, `[edit]`, `[agent]`, `[turn]`, `[result]`,
  `[error]`), skipping noisy token-accounting heartbeats while keeping plain
  test/command text lines intact and redacted.
- **Live follow (`--follow` / `-f`)**:
  Stream the worker header, initial tail lines, and newly appended complete log
  lines to `stdout` as the worker runs, emitting `[stage]` notices whenever the
  worker transitions across stages or opens a new log (including live suite
  validation logs). Stop cleanly with exit code `0` when the job finishes (or
  has no live process while the Autopilot timer is off) or when `signal` /
  `SIGINT` / `SIGTERM` detaches the viewer. Detaching prints a confirmation
  that the background worker continues untouched.

## Dependencies

- [Autopilot core](autopilot-core.prompt.md): required context for `jobs/N.json`,
  `core.json`, `logs/` and `history.jsonl` state shapes.
- [Shared full-suite queue](test-suite-queue.prompt.md): required context for
  read-only `readSuiteProgress` queue and validation-log inspection.
- [Repository Autopilot settings](autopilot.prompt.md): required context for
  `pdd.json` mode display and CLI subcommand routing.
- [Secret redaction](secret-redaction.prompt.md): required for redacting
  displayed log lines and diagnostics.
