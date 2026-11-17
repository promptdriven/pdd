# Autopilot worker logs

Own `src/autopilot-logs.mjs`. Export `runAutopilotLogs(input, ports)`,
`inspectAutopilotWorkers(input, ports)`, `formatWorkerLogLine(line, secrets)`
and `parseIssueSelector(raw)`. Give a person a supported read-only way to list
headless Autopilot workers, inspect a worker's stage, process state, queue
position, blockers and saved evidence, and follow live worker output from the
terminal without knowing internal state folders or touching running jobs.

## Domain decisions

- **Strictly read-only inspection and `observe`-mode preservation**:
  Viewing worker logs never creates, modifies or deletes files in the checkout,
  Autopilot state folders, validation folders, or user configuration, never
  calls `gh`, and never approves gates or alters `observe`, `auto` or `off`
  modes.
- **Same-user worker PID liveness boundary**:
  Accept only safe integer PIDs with `pid > 1` across worker handles and
  `suite.childPid`. In default liveness checks, any error from `kill(pid, 0)`
  (both `ESRCH` and `EPERM`) returns `false` so system init (`pid 1`) or another
  user's process is never reported as a running Autopilot worker; when a job
  token is present, `ps` command output must also include that token.
- **End-to-end secret redaction and line-aligned UTF-8 reads**:
  Derive caller secrets with `knownSecretValues(env)` (including injected
  `input.env`), strip ANSI/control characters, and run `redactSecrets(..., secrets)`
  across human snapshots, `--follow` streams, and `--json` payloads — covering
  log lines, worker metadata (`agentKind`, `signal`, `wakeAt`, `holder`,
  `verdict`, `head`, `repo`, `gitRoot`) and file path strings (`logPaths`,
  `evidencePaths`, `streams[].path`, `suite.logPath`, `suite.receiptPath`).
  Align tail and incremental follow reads on `\n` (`0x0a`) byte boundaries
  (expanding read windows up to 16 MiB and ignoring a trailing EOF newline when
  locating the start of the tail window) so multi-byte UTF-8 codepoints and
  secret prefixes are never split mid-line and single-line tails ending in `\n`
  are never dropped.
- **Bounded, pipe-safe `--follow` polling**:
  Resolve `git rev-parse --show-toplevel` once and pass `gitRoot` into poll
  iterations instead of spawning `git` on every poll. Attach `close` and `error`
  (`EPIPE`) handlers on `stdout` and guard writes on `!stdout.destroyed &&
  !stdout.writableEnded` so piped commands (`| head -n 5`) detach cleanly with
  exit `0`, no `EPIPE` crash, no trailing detach message to a closed pipe, and
  no leaked poll timer. Enforce `maxDurationMs` (default `3_600_000` ms / 60
  minutes) so unattended follow sessions always terminate cleanly.

## Safety and observe mode

Every operation in this module is strictly read-only:

- Never write, create, rename or delete files in the repository, Autopilot
  state folders, validation folders, or user configuration.
- Never approve gates, merge pull requests, claim or release issues, wake
  scheduler ticks, or call GitHub (`gh`). Viewing preserves `observe`, `auto`
  and `off` modes unchanged.
- Check process liveness read-only (`pid > 1`, `kill(pid, 0)` returning `false`
  on any error including `EPERM` and `ESRCH`, and `ps` command match on the
  job's `.spec.json` token when present). Never send `SIGTERM`, `SIGKILL`,
  `SIGINT` or any stopping signal to a worker or test-suite process.
- Redact credentials and tokens in every displayed log line, JSON field, error
  note and path summary with `redactSecrets(..., knownSecretValues(env))`. Strip
  terminal escape and control sequences so output is safe in interactive
  terminals, pipes and redirected files.

## CLI contract

`runAutopilotLogs({cwd, env, issue, follow, lines, json}, ports)` accepts:

- `issue`: optional issue selector from the positional `[ISSUE]` operand or
  `--issue N` (`17`, `#17`, `owner/repo#17`, or a GitHub issue URL). When both
  positional and `--issue` selectors are supplied directly, compare their parsed
  issue numbers and optional repository qualifiers; conflicting selectors, a
  blank/invalid selector, or `--follow` together with `--json` returns exit code
  `2` with one clear usage message before state inspection.
- `follow`: Boolean from `--follow` or `-f`. Requires a selected issue; calling
  `--follow` with no issue returns exit code `2` explaining how to pass an
  issue (`pdd autopilot logs ISSUE --follow`).
- `lines`: positive integer tail count from `--lines N` (default `40`, range
  `1` to `5000`).
- `json`: Boolean from `--json` for structured machine-readable inspection.

Injectable `ports` provide `fs`, `git(args, {cwd, env})`, `gitRoot`, `now()`,
`stateRoot`, `coreRoot`, `isProcessAlive(pid, token)`, `readSuite({cwd, env})`,
`stdout`, `signal`, `pollMs` (default `250`), `maxDurationMs` (default
`3600000`) and `sleep(ms)`. Resolve the repository root with
`git rev-parse --show-toplevel` under `LC_ALL=C` and `LANG=C` unless
`ports.gitRoot` is already supplied. Outside a Git repository, return
`{exitCode: 1, message: "This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run the command again."}`.
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
  lines to `stdout` as the worker runs, reusing the resolved `gitRoot` on poll
  ticks and emitting `[stage]` notices whenever the worker transitions across
  stages or opens a new log (including live suite validation logs). Stop cleanly
  with exit code `0` when the job finishes (or has no live process while the
  Autopilot timer is off), when `maxDurationMs` elapses, when `stdout` closes or
  errors (`EPIPE`), or when `signal` / `SIGINT` / `SIGTERM` detaches the viewer.
  When `stdout` is still writable on signal detach, print a confirmation that
  the background worker continues untouched.

## Dependencies

- [Autopilot core](autopilot-core.prompt.md): required context for `jobs/N.json`,
  `core.json`, `logs/` and `history.jsonl` state shapes.
- [Shared full-suite queue](test-suite-queue.prompt.md): required context for
  read-only `readSuiteProgress` queue and validation-log inspection.
- [Secret redaction](secret-redaction.prompt.md): required for redacting
  displayed log lines, JSON payloads, metadata and path summaries.
